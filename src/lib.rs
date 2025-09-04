use std::borrow::BorrowMut;
use std::intrinsics::mir::CastPtrToPtr;
use std::ptr::{null, null_mut};

use vstd::layout::layout_for_type_is_valid;
use vstd::{compute, prelude::*};

use vstd::raw_ptr::{
    allocate, deallocate, ptr_mut_read, ptr_mut_write, ptr_null_mut, Dealloc, PointsTo,
};

verus! {

struct LNode<T> {
    next: *mut LNode<T>,
    prev: *mut LNode<T>,
    value: T
}

struct LinkedList<T> {
    head: *mut LNode<T>,
    tail: *mut LNode<T>,
    tokens: Tracked<Seq<PointsTo<LNode<T>>>>,
    dealloc: Tracked<Seq<Dealloc>>,
}

spec fn dealloc_condition<T>(dealloc: Dealloc, token: PointsTo<LNode<T>>) -> bool {
    &&& dealloc.size() == size_of::<LNode<T>>()
    &&& dealloc.align() == align_of::<LNode<T>>()
    &&& dealloc.addr() == token.ptr()@.addr
    &&& dealloc.provenance() == token.ptr()@.provenance
}

spec fn dealloc_tokens<T>(dealloc: Seq<Dealloc>, tokens: Seq<PointsTo<LNode<T>>>) -> bool
{
    forall |i: int| 0 <= i < tokens.len() ==> dealloc_condition(#[trigger] dealloc[i], tokens[i])
}

spec fn forward_linked<T>(ptr: *mut LNode<T>, seq: Seq<PointsTo<LNode<T>>>) -> bool
decreases seq.len()
{
    if seq.len() == 0 {
        ptr@.addr == 0
    }
    else {
        &&& ptr@.addr != 0
        &&& seq.first().ptr() == ptr
        &&& seq.first().is_init()
        &&& forward_linked(seq.first().value().next, seq.drop_first())
    }
}

spec fn backward_linked<T>(ptr: *mut LNode<T>, seq: Seq<PointsTo<LNode<T>>>) -> bool
decreases seq.len()
{
    if seq.len() == 0 {
        ptr@.addr == 0
    }
    else {
        &&& ptr@.addr != 0
        &&& seq.last().ptr() == ptr
        &&& seq.last().is_init()
        &&& backward_linked(seq.last().value().prev, seq.drop_last())
    }
}

proof fn lemma_backward_linked_after_push_front<T>(
    pre: Seq<PointsTo<LNode<T>>>,
    new: PointsTo<LNode<T>>,
    post: Seq<PointsTo<LNode<T>>>,
)
requires
    backward_linked(pre.last().ptr(), pre),
    new.ptr()@.addr != 0,
    new.is_init(),
    new.value().prev@.addr == 0,
    post.len() > 0,
    pre.len() > 0,
    post[0].ptr() == pre[0].ptr(),
    post[0].is_init(),
    post[0].value().prev == new.ptr(),
    post.remove(0) == pre.remove(0)
ensures
    backward_linked(pre.last().ptr(), post.insert(0, new))
decreases
    pre.len()
{
    if pre.len() > 1 {
        assert(post.remove(0).last() == post.last());
        assert(pre.remove(0).last() == pre.last());
        assert(pre.drop_last().remove(0) == pre.remove(0).drop_last());
        assert(post.drop_last().remove(0) == post.remove(0).drop_last());

        let prev = pre.last().value().prev;
        assert(backward_linked(prev, pre.drop_last()));
        assert(pre.drop_last().last().ptr() == prev);
        lemma_backward_linked_after_push_front(pre.drop_last(), new, post.drop_last());
        assert(post.drop_last().insert(0, new) == post.insert(0, new).drop_last());
        assert(backward_linked(prev, post.drop_last().insert(0, new)));
        assert(backward_linked(pre.last().ptr(), post.insert(0, new)));
    }
    else {
        assert(pre.last().ptr() == post.first().ptr());
        assert(backward_linked(new.value().prev, seq![new].drop_last()));
        assert(backward_linked(post.first().value().prev, seq![new]));
        assert(post.insert(0, new).drop_last() == seq![new]);
    }
}

proof fn lemma_forward_linked_after_pop_back<T>(
    pre: Seq<PointsTo<LNode<T>>>,
    post: Seq<PointsTo<LNode<T>>>,
)
requires
    forward_linked(pre.first().ptr(), pre),
    post.len() > 0,
    pre.len() > 1,
    post.drop_last() == pre.drop_last().drop_last(),
    post.last().is_init(),
    post.last().value().next@.addr == 0,
    post.last().ptr() == pre.drop_last().last().ptr(),
ensures
    forward_linked(pre.first().ptr(), post)
decreases
    pre.len()
{
    if post.len() == 1 {
        assert(pre.drop_last().drop_last().len() == 0);
        assert(pre.first().ptr() == pre.drop_last().last().ptr());

        assert(forward_linked(post.last().value().next, post.drop_first()));
        assert(forward_linked(pre.first().ptr(), post));
    }
    else {
        assert(pre.drop_last().drop_last().len() > 0);
        assert(pre.drop_first().drop_last().drop_last() == pre.drop_last().drop_last().drop_first());
        assert(post.drop_first().drop_last() == post.drop_last().drop_first());

        assert(forward_linked(pre.first().value().next, pre.drop_first()));
        assert(pre.drop_first().first().ptr() == pre.first().value().next);
        lemma_forward_linked_after_pop_back(pre.drop_first(), post.drop_first());

        assert(pre.first() == pre.drop_last().drop_last().first());
    }
}

impl<T> LinkedList<T> {
    pub closed spec fn wf(&self) -> bool {
        &&& forward_linked(self.head, self.tokens@)
        &&& backward_linked(self.tail, self.tokens@)
        &&& dealloc_tokens(self.dealloc@, self.tokens@)
        &&& self.dealloc@.len() == self.tokens@.len()
    }

    pub closed spec fn view(&self) -> Seq<T>
    {
        self.tokens@.map_values(|t: PointsTo<LNode<T>>| t.value().value)
    }

    pub fn new() -> (r: Self)
    ensures r.wf(), r@.len() == 0
    {
        LinkedList {
            head: null_mut(),
            tail: null_mut(),
            tokens: Tracked(Seq::tracked_empty()),
            dealloc: Tracked(Seq::tracked_empty())
        }
    }

    pub fn push_front(&mut self, value: T)
    requires old(self).wf()
    ensures
        self.wf(),
        self@ == old(self)@.insert(0, value)
    {
        let new_node = LNode { next: self.head, prev: null_mut(), value };

        layout_for_type_is_valid::<LNode<T>>();

        assume(size_of::<LNode<T>>() != 0);
        let (ptr, Tracked(raw_perm), Tracked(dealloc_perm)) = allocate(size_of::<LNode<T>>(), align_of::<LNode<T>>());

        let tracked perm = raw_perm.into_typed::<LNode<T>>(ptr.addr());
        let ptr: *mut LNode<T> = ptr as _;
        let tracked _ = perm.is_nonnull();

        ptr_mut_write(ptr, Tracked(&mut perm), new_node);

        if self.head as usize == 0 {
            self.tail = ptr;

            assert(self.tokens@.insert(0, perm).drop_last() =~= seq![]);
            assert(backward_linked(new_node.prev, seq![]));
        }
        else {
            let tracked next_perm = self.tokens.borrow_mut().tracked_pop_front();
            let mut next_node: LNode<T> = ptr_mut_read(self.head, Tracked(&mut next_perm));
            next_node.prev = ptr;
            ptr_mut_write(self.head, Tracked(&mut next_perm), next_node);
            let tracked _ = self.tokens.borrow_mut().tracked_insert(0, next_perm);

            assert(self.tokens@.remove(0) == old(self).tokens@.remove(0));
            assert(forward_linked(self.head, self.tokens@));

            let tracked _ = lemma_backward_linked_after_push_front(
                old(self).tokens@, perm, self.tokens@);

            assert(dealloc_condition(self.dealloc@.first(), self.tokens@.first()));
        }

        self.head = ptr;
        assert(self.tokens@.insert(0, perm).remove(0) =~= self.tokens@);
        let tracked _ = self.tokens.borrow_mut().tracked_insert(0, perm);
        let tracked _ = self.dealloc.borrow_mut().tracked_insert(0, dealloc_perm);

        assert(dealloc_condition(dealloc_perm, perm));
    }

    pub fn pop_back(&mut self) -> (value: T)
    requires old(self).wf(), old(self)@.len() > 0
    ensures
        self.wf(),
        value == old(self)@.last(),
        self@ == old(self)@.drop_last(),
    {
        let tracked perm = self.tokens.borrow_mut().tracked_pop();
        let node = ptr_mut_read(self.tail, Tracked(&mut perm));

        let tracked dealloc_perm = self.dealloc.borrow_mut().tracked_pop();
        deallocate(
            self.tail as _,
            size_of::<LNode<T>>(),
            align_of::<LNode<T>>(),
            Tracked(perm.into_raw()),
            Tracked(dealloc_perm)
        );

        self.tail = node.prev;
        assert(backward_linked(self.tail, self.tokens@));

        if self.tail as usize == 0 {
            self.head = null_mut();
        }
        else {
            let tracked prev_perm = self.tokens.borrow_mut().tracked_pop();
            let mut prev = ptr_mut_read(self.tail, Tracked(&mut prev_perm));
            prev.next = null_mut();
            ptr_mut_write(self.tail, Tracked(&mut prev_perm), prev);
            let tracked _ = self.tokens.borrow_mut().tracked_push(prev_perm);

            assert(self.tokens@.drop_last() =~= old(self).tokens@.drop_last().drop_last());
            let tracked _ = lemma_forward_linked_after_pop_back(old(self).tokens@, self.tokens@);
        }

        node.value
    }
}

} // verus!
