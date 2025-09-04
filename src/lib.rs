use std::borrow::BorrowMut;
use std::intrinsics::mir::CastPtrToPtr;
use std::ptr::{null, null_mut};

use vstd::layout::layout_for_type_is_valid;
use vstd::{compute, prelude::*};

use vstd::raw_ptr::{
    allocate, deallocate, ptr_mut_read, ptr_mut_write, ptr_null_mut, ptr_ref, Dealloc, PointsTo,
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

impl<T> LinkedList<T> {
    spec fn wf_perm(&self, i: int) -> bool {
        &&& if i + 1 < self@.len() {
            &&& self.tokens@[i].value().next == self.tokens@[i + 1].ptr()
            &&& self.tokens@[i].value().next@.addr != 0
        } else {
            &&& self.tokens@[i].value().next@.addr == 0
            &&& self.tail == self.tokens@[i].ptr()
        }
        &&& if i > 0 {
            &&& self.tokens@[i].value().prev == self.tokens@[i - 1].ptr()
            &&& self.tokens@[i].value().prev@.addr != 0
        } else {
            &&& self.tokens@[i].value().prev@.addr == 0
            &&& self.head == self.tokens@[i].ptr()
        }
        &&& self.tokens@[i].is_init()
        &&& self.dealloc@[i].addr() == self.tokens@[i].ptr()@.addr
        &&& self.dealloc@[i].provenance() == self.tokens@[i].ptr()@.provenance
        &&& self.dealloc@[i].size() == size_of::<LNode<T>>()
        &&& self.dealloc@[i].align() == align_of::<LNode<T>>()
    }

    pub closed spec fn wf(&self) -> bool {
        &&& forall |i: int| 0 <= i < self.tokens@.len() ==> self.wf_perm(i)
        &&& self.dealloc@.len() == self.tokens@.len()
        &&& self.head@.addr != 0 <==> self.tokens@.len() > 0
        &&& self.head@.addr != 0 ==> self.head == self.tokens@.first().ptr()
        &&& self.tail@.addr != 0 <==> self.tokens@.len() > 0
        &&& self.tail@.addr != 0 ==> self.tail == self.tokens@.last().ptr()
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
        layout_for_type_is_valid::<LNode<T>>();
        assume(size_of::<LNode<T>>() != 0);
        let (ptr, Tracked(raw_perm), Tracked(dealloc_perm)) = allocate(size_of::<LNode<T>>(), align_of::<LNode<T>>());

        let tracked perm = raw_perm.into_typed::<LNode<T>>(ptr.addr());
        let ptr: *mut LNode<T> = ptr as _;
        let tracked _ = perm.is_nonnull();

        let new_node = LNode { next: self.head, prev: null_mut(), value };
        ptr_mut_write(ptr, Tracked(&mut perm), new_node);

        if self.head as usize == 0 {
            self.tail = ptr;
        }
        else {
            assert(self.wf_perm(0));
            let tracked next_perm = self.tokens.borrow_mut().tracked_pop_front();
            let mut next_node: LNode<T> = ptr_mut_read(self.head, Tracked(&mut next_perm));
            next_node.prev = ptr;
            ptr_mut_write(self.head, Tracked(&mut next_perm), next_node);
            let tracked _ = self.tokens.borrow_mut().tracked_insert(0, next_perm);
        }

        self.head = ptr;
        let tracked _ = self.tokens.borrow_mut().tracked_insert(0, perm);
        let tracked _ = self.dealloc.borrow_mut().tracked_insert(0, dealloc_perm);

        assert forall |i: int| 0 < i < self.tokens@.len()
        implies self.wf_perm(i)
        by { assert(old(self).wf_perm(i - 1)); };
    }

    pub fn pop_back(&mut self) -> (value: T)
    requires old(self).wf(), old(self)@.len() > 0
    ensures
        self.wf(),
        value == old(self)@.last(),
        self@ == old(self)@.drop_last(),
    {
        assert(self.wf_perm(self@.len() - 1));
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

        if self.tail as usize == 0 {
            assert(old(self)@.len() == 1);
            self.head = null_mut();
        }
        else {
            assert(old(self).wf_perm(old(self)@.len() - 2));
            let tracked prev_perm = self.tokens.borrow_mut().tracked_pop();
            let mut prev = ptr_mut_read(self.tail, Tracked(&mut prev_perm));
            prev.next = null_mut();
            ptr_mut_write(self.tail, Tracked(&mut prev_perm), prev);
            let tracked _ = self.tokens.borrow_mut().tracked_push(prev_perm);

            assert forall |i: int| 0 <= i < self.tokens@.len()
            implies self.wf_perm(i)
            by { assert(old(self).wf_perm(i)); };
        }

        node.value
    }

    pub fn peek_back(&self) -> (result: Option<&T>)
    requires self.wf()
    ensures
        match result {
            Some(value) => value == self@.last() && self@.len() > 0,
            None => self@.len() == 0
        }
    {
        if self.tail as usize == 0 { None }
        else {
            assert(self.wf_perm(self@.len() - 1));
            let tracked perm = self.tokens.borrow().tracked_borrow(self.tokens@.len() - 1);
            Some(&ptr_ref::<LNode<T>>(self.tail as _, Tracked(perm)).value)
        }
    }

}

} // verus!
