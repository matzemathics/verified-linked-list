use std::borrow::BorrowMut;
use std::ptr::null_mut;

use vstd::layout::layout_for_type_is_valid;
use vstd::prelude::*;

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
    tokens: Tracked<Seq<PermData<T>>>,
}

tracked struct PermData<T> {
    access: PointsTo<LNode<T>>,
    dealloc: Dealloc,
}

impl<T> PermData<T> {
    spec fn valid(&self) -> bool {
        &&& self.access.is_init()
        &&& self.dealloc.addr() == self.access.ptr()@.addr
        &&& self.dealloc.provenance() == self.access.ptr()@.provenance
        &&& self.dealloc.size() == size_of::<LNode<T>>()
        &&& self.dealloc.align() == align_of::<LNode<T>>()
    }

    spec fn next(&self) -> *mut LNode<T> {
        self.access.value().next
    }

    spec fn prev(&self) -> *mut LNode<T> {
        self.access.value().prev
    }

    spec fn ptr(&self) -> *mut LNode<T> {
        self.access.ptr()
    }

    spec fn value(&self) -> T {
        self.access.value().value
    }
}

impl<T> LinkedList<T> {
    spec fn wf_perm(&self, i: int) -> bool {
        &&& if i + 1 < self@.len() {
            &&& self.tokens@[i].next() == self.tokens@[i + 1].ptr()
            &&& self.tokens@[i].next()@.addr != 0
        } else {
            &&& self.tokens@[i].next()@.addr == 0
            &&& self.tail == self.tokens@[i].ptr()
        }
        &&& if i > 0 {
            &&& self.tokens@[i].prev() == self.tokens@[i - 1].ptr()
            &&& self.tokens@[i].prev()@.addr != 0
        } else {
            &&& self.tokens@[i].prev()@.addr == 0
            &&& self.head == self.tokens@[i].ptr()
        }
        &&& self.tokens@[i].valid()
    }

    pub closed spec fn wf(&self) -> bool {
        &&& forall |i: int| 0 <= i < self.tokens@.len() ==> self.wf_perm(i)
        &&& self.head@.addr != 0 <==> self.tokens@.len() > 0
        &&& self.tail@.addr != 0 <==> self.tokens@.len() > 0
    }

    pub closed spec fn view(&self) -> Seq<T> {
        self.tokens@.map_values(|t: PermData<T>| t.value())
    }

    pub fn new() -> (r: Self)
    ensures r.wf(), r@.len() == 0
    {
        LinkedList {
            head: null_mut(),
            tail: null_mut(),
            tokens: Tracked(Seq::tracked_empty()),
        }
    }

    fn allocate_node(val: LNode<T>) -> (res: (*mut LNode<T>, Tracked<PermData<T>>))
    ensures
        res.0@.addr != 0,
        res.0 == res.1@.ptr(),
        res.1@.access.value() == val,
        res.1@.valid()
    {
        layout_for_type_is_valid::<LNode<T>>();
        assume(size_of::<LNode<T>>() != 0);
        let (ptr, Tracked(raw_perm), Tracked(dealloc)) = allocate(size_of::<LNode<T>>(), align_of::<LNode<T>>());

        let tracked access = raw_perm.into_typed::<LNode<T>>(ptr.addr());
        let ptr: *mut LNode<T> = ptr as _;
        let tracked _ = access.is_nonnull();

        ptr_mut_write(ptr, Tracked(&mut access), val);
        (ptr, Tracked(PermData { access, dealloc }))
    }

    pub fn push_front(&mut self, value: T)
    requires old(self).wf()
    ensures
        self.wf(),
        self@ == old(self)@.insert(0, value)
    {
        let (ptr, Tracked(pd)) = Self::allocate_node(LNode {
            value,
            prev: null_mut(),
            next: self.head,
        });

        if self.tail as usize == 0 {
            self.tail = ptr;
        }
        else {
            assert(self.wf_perm(0));
            let tracked PermData { access, dealloc } = self.tokens.borrow_mut().tracked_pop_front();
            let mut next_node: LNode<T> = ptr_mut_read(self.head, Tracked(&mut access));
            next_node.prev = ptr;
            ptr_mut_write(self.head, Tracked(&mut access), next_node);
            let tracked _ = self.tokens.borrow_mut().tracked_insert(0, PermData { access, dealloc });
        }

        self.head = ptr;
        let tracked _ = self.tokens.borrow_mut().tracked_insert(0, pd);

        assert forall |i: int| 0 < i < self.tokens@.len()
        implies self.wf_perm(i)
        by { assert(old(self).wf_perm(i - 1)); };
    }

    pub fn push_back(&mut self, value: T)
    requires old(self).wf()
    ensures
        self.wf(),
        self@ == old(self)@.push(value)
    {
        let (ptr, Tracked(pd)) = Self::allocate_node(LNode {
            value,
            prev: self.tail,
            next: null_mut(),
        });

        if self.head as usize == 0 {
            self.head = ptr;
        }
        else {
            assert(self.wf_perm(self@.len() - 1));
            let tracked PermData { access, dealloc } = self.tokens.borrow_mut().tracked_pop();
            let mut prev_node: LNode<T> = ptr_mut_read(self.tail, Tracked(&mut access));
            prev_node.next = ptr;
            ptr_mut_write(self.tail, Tracked(&mut access), prev_node);
            let tracked _ = self.tokens.borrow_mut().tracked_push(PermData { access, dealloc });
        }

        self.tail = ptr;
        let tracked _ = self.tokens.borrow_mut().tracked_push(pd);

        assert forall |i: int| 0 <= i < self.tokens@.len() - 1
        implies self.wf_perm(i)
        by { assert(old(self).wf_perm(i)); };
    }

    pub fn pop_back(&mut self) -> (value: T)
    requires old(self).wf(), old(self)@.len() > 0
    ensures
        self.wf(),
        value == old(self)@.last(),
        self@ == old(self)@.drop_last(),
    {
        assert(self.wf_perm(self@.len() - 1));
        let tracked PermData { access, dealloc } = self.tokens.borrow_mut().tracked_pop();
        let node = ptr_mut_read(self.tail, Tracked(&mut access));

        deallocate(
            self.tail as _,
            size_of::<LNode<T>>(),
            align_of::<LNode<T>>(),
            Tracked(access.into_raw()),
            Tracked(dealloc)
        );

        self.tail = node.prev;

        if self.tail as usize == 0 {
            assert(old(self)@.len() == 1);
            self.head = null_mut();
        }
        else {
            assert(old(self).wf_perm(old(self)@.len() - 2));
            let tracked PermData { access, dealloc } = self.tokens.borrow_mut().tracked_pop();
            let mut prev = ptr_mut_read(self.tail, Tracked(&mut access));
            prev.next = null_mut();
            ptr_mut_write(self.tail, Tracked(&mut access), prev);
            let tracked _ = self.tokens.borrow_mut().tracked_push(PermData { access, dealloc });

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
            Some(&ptr_ref::<LNode<T>>(self.tail as _, Tracked(&perm.access)).value)
        }
    }

}

} // verus!
