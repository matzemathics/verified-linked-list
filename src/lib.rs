use vstd::prelude::*;

use vstd::simple_pptr::{PPtr, PointsTo};

verus! {

struct LNode<T> {
    next: usize,
    prev: usize,
    value: T
}

struct LinkedList<T> {
    head: PPtr<LNode<T>>,
    tail: PPtr<LNode<T>>,
    tokens: Tracked<Seq<PointsTo<LNode<T>>>>
}

spec fn forward_linked<T>(ptr: usize, seq: Seq<PointsTo<LNode<T>>>) -> bool
decreases seq.len()
{
    if seq.len() == 0 {
        ptr == 0
    }
    else {
        &&& ptr != 0
        &&& seq[0].addr() == ptr
        &&& seq[0].is_init()
        &&& forward_linked(seq[0].value().next, seq.remove(0))
    }
}

spec fn backward_linked<T>(ptr: usize, seq: Seq<PointsTo<LNode<T>>>) -> bool
decreases seq.len()
{
    if seq.len() == 0 {
        ptr == 0
    }
    else {
        &&& ptr != 0
        &&& seq.last().addr() == ptr
        &&& seq.last().is_init()
        &&& backward_linked(seq.last().value().prev, seq.drop_last())
    }
}

proof fn lemma_backward_linked_after_push_front<T>(
    tail: usize,
    pre: Seq<PointsTo<LNode<T>>>,
    new: PointsTo<LNode<T>>,
    post: Seq<PointsTo<LNode<T>>>,
)
requires
    backward_linked(tail, pre),
    new.addr() != 0,
    new.is_init(),
    new.value().prev == 0,
    post.len() > 0,
    pre.len() > 0,
    post[0].addr() == pre[0].addr(),
    post[0].is_init(),
    post[0].value().prev == new.addr(),
    post.remove(0) == pre.remove(0)
ensures
    backward_linked(tail, post.insert(0, new))
decreases
    pre.len()
{
    if pre.len() > 1 {
        assert(post.remove(0).last() == post.last());
        assert(pre.remove(0).last() == pre.last());
        assert(pre.drop_last().remove(0) == pre.remove(0).drop_last());
        assert(post.drop_last().remove(0) == post.remove(0).drop_last());

        let prev = pre.last().value().prev;
        lemma_backward_linked_after_push_front(prev, pre.drop_last(), new, post.drop_last());
        assert(post.drop_last().insert(0, new) == post.insert(0, new).drop_last());
        assert(backward_linked(prev, post.drop_last().insert(0, new)));
        assert(backward_linked(tail, post.insert(0, new)));
    }
    else {
        assert(tail == post[0].addr());
        assert(backward_linked(0, seq![new].drop_last()));
        assert(backward_linked(post[0].value().prev, seq![new]));
        assert(post.insert(0, new).drop_last() == seq![new]);
    }
}

impl<T> LinkedList<T> {
    pub closed spec fn wf(&self) -> bool {
        &&& forward_linked(self.head.addr(), self.tokens@)
        &&& backward_linked(self.tail.addr(), self.tokens@)
    }

    pub closed spec fn view(&self) -> Seq<T>
    {
        self.tokens@.map_values(|t: PointsTo<LNode<T>>| t.value().value)
    }

    pub fn push_front(&mut self, value: T)
    requires old(self).wf()
    ensures
        self.wf(),
        self@ == old(self)@.insert(0, value)
    {
        let new_node = LNode { next: self.head.addr(), prev: 0, value };
        let (ptr, Tracked(perm)) = PPtr::new(new_node);
        let tracked _ = perm.is_nonnull();

        if self.head.addr() == 0 { self.tail = ptr; }
        else {
            let tracked next_perm = self.tokens.borrow_mut().tracked_remove(0);
            let mut next_node: LNode<T> = self.head.take(Tracked(&mut next_perm));
            next_node.prev = ptr.addr();
            self.head.put(Tracked(&mut next_perm), next_node);
            let tracked _ = self.tokens.borrow_mut().tracked_insert(0, next_perm);

            assert(self.tokens@.remove(0) == old(self).tokens@.remove(0));
            assert(forward_linked(self.head.addr(), self.tokens@));

            let tracked _ = lemma_backward_linked_after_push_front(
                self.tail.addr(), old(self).tokens@, perm, self.tokens@);
        }

        self.head = ptr;
        assert(self.tokens@.insert(0, perm).remove(0) =~= self.tokens@);
        let tracked _ = self.tokens.borrow_mut().tracked_insert(0, perm);
    }
}

} // verus!
