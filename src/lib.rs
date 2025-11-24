use std::ptr::null_mut;

use vstd::layout::layout_for_type_is_valid;
use vstd::prelude::*;

use vstd::raw_ptr::{
    allocate, deallocate, ptr_mut_read, ptr_mut_write, ptr_ref, Dealloc, PointsTo,
};

#[cfg(verus_keep_ghost)]
use vstd::raw_ptr::ptr_null_mut; 

verus! {

struct LNode<T> {
    next: *mut LNode<T>,
    prev: *mut LNode<T>,
    value: T
}

pub struct LinkedList<T> {
    head: *mut LNode<T>,
    tail: *mut LNode<T>,
    _tokens: Tracked<Seq<PermData<T>>>,
}

tracked struct PermData<T> {
    _access: PointsTo<LNode<T>>,
    _dealloc: Dealloc,
}

impl<T> PermData<T> {
    spec fn valid(&self) -> bool {
        &&& self._access.is_init()
        &&& self._access.ptr()@.addr != 0
        &&& self._dealloc.addr() == self._access.ptr()@.addr
        &&& self._dealloc.provenance() == self._access.ptr()@.provenance
        &&& self._dealloc.size() == size_of::<LNode<T>>()
        &&& self._dealloc.align() == align_of::<LNode<T>>()
    }

    spec fn next(&self) -> *mut LNode<T> {
        self._access.value().next
    }

    spec fn prev(&self) -> *mut LNode<T> {
        self._access.value().prev
    }

    spec fn ptr(&self) -> *mut LNode<T> {
        self._access.ptr()
    }

    spec fn value(&self) -> T {
        self._access.value().value
    }
}

impl<T> LinkedList<T> {
    spec fn next_link(&self, i: int) -> bool {
        if i + 1 < self@.len() {
            &&& self._tokens@[i].next() == self.tokens@[i + 1].ptr()
        } else {
            &&& self._tokens@[i].next()@.addr == 0
            &&& self.tail == self._tokens@[i].ptr()
        }
    }

    spec fn prev_link(&self, i: int) -> bool {
        if i > 0 {
            &&& self._tokens@[i].prev() == self._tokens@[i - 1].ptr()
        } else {
            &&& self._tokens@[i].prev()@.addr == 0
            &&& self.head == self._tokens@[i].ptr()
        }
    }


    spec fn wf_perm(&self, i: int) -> bool {
        &&& self.next_link(i)
        &&& self.prev_link(i)
        &&& self._tokens@[i].valid()
    }

    pub closed spec fn wf(&self) -> bool {
        &&& forall |i: int| 0 <= i < self._tokens@.len() ==> self.wf_perm(i)
        &&& self.head@.addr != 0 <==> self._tokens@.len() > 0
        &&& self.tail@.addr != 0 <==> self._tokens@.len() > 0
    }

    pub closed spec fn view(&self) -> Seq<T> {
        self._tokens@.map_values(|t: PermData<T>| t.value())
    }

    pub fn new() -> (r: Self)
    ensures r.wf(), r@.len() == 0
    {
        LinkedList {
            head: null_mut(),
            tail: null_mut(),
            _tokens: Tracked(Seq::tracked_empty()),
        }
    }

    fn allocate_node(val: LNode<T>) -> (res: (*mut LNode<T>, Tracked<PermData<T>>))
    ensures
        res.0@.addr != 0,
        res.0 == res.1@.ptr(),
        res.1@._access.value() == val,
        res.1@.valid()
    {
        layout_for_type_is_valid::<LNode<T>>();
        assume(size_of::<LNode<T>>() != 0);
        let (ptr, Tracked(raw_perm), Tracked(_dealloc)) = allocate(size_of::<LNode<T>>(), align_of::<LNode<T>>());

        let tracked _access = raw_perm.into_typed::<LNode<T>>(ptr.addr());
        let ptr: *mut LNode<T> = ptr as _;
        let tracked _ = _access.is_nonnull();

        ptr_mut_write(ptr, Tracked(&mut _access), val);
        (ptr, Tracked(PermData { _access, _dealloc }))
    }

    pub fn push_front(&mut self, value: T)
    requires old(self).wf()
    ensures self.wf(), self@ == old(self)@.insert(0, value)
    {
        let (ptr, Tracked(pd)) = Self::allocate_node(LNode {
            value,
            prev: null_mut(),
            next: self.head,
        });

        if self.tail as usize == 0 { self.tail = ptr; }
        else { self.update_head(|head: LNode<T>| -> (res: LNode<T>)
                ensures res.prev == ptr, res.value == head.value, res.next == head.next
                { LNode { prev: ptr, ..head } }); }

        self.head = ptr;
        let tracked _ = self._tokens.borrow_mut().tracked_insert(0, pd);

        proof!{
            if old(self)@.len() != 0 { assert(old(self).wf_perm(0)); }

            assert forall |i: int| 0 < i < self._tokens@.len()
            implies self.wf_perm(i)
            by { assert(old(self).wf_perm(i - 1)); };
        }
    }

    fn update_head(&mut self, f: impl Fn(LNode<T>) -> LNode<T>)
    requires
        old(self)@.len() > 0,
        old(self).wf_perm(0),
        f.requires((old(self)._tokens@[0]._access.value(),)),
    ensures
        f.ensures((old(self)._tokens@[0]._access.value(),), self._tokens@[0]._access.value()),
        self._tokens@[0]._access.ptr() == old(self)._tokens@[0]._access.ptr(),
        self._tokens@[0].valid(),
        forall |i: int| #![auto] 0 < i < self._tokens@.len() ==> self._tokens@[i] == old(self)._tokens@[i],
        self._tokens@.len() == old(self)._tokens@.len(),
        self.head == old(self).head,
        self.tail == old(self).tail,
    {
        let tracked PermData { _access, _dealloc } = self._tokens.borrow_mut().tracked_pop_front();
        let mut node: LNode<T> = ptr_mut_read(self.head, Tracked(&mut _access));
        node = f(node);
        ptr_mut_write(self.head, Tracked(&mut _access), node);
        let tracked _ = self._tokens.borrow_mut().tracked_insert(0, PermData { _access, _dealloc });
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
            let tracked PermData { _access, _dealloc } = self._tokens.borrow_mut().tracked_pop();
            let mut prev_node: LNode<T> = ptr_mut_read(self.tail, Tracked(&mut _access));
            prev_node.next = ptr;
            ptr_mut_write(self.tail, Tracked(&mut _access), prev_node);
            let tracked _ = self._tokens.borrow_mut().tracked_push(PermData { _access, _dealloc });
        }

        self.tail = ptr;
        let tracked _ = self._tokens.borrow_mut().tracked_push(pd);

        assert forall |i: int| 0 <= i < self._tokens@.len() - 1
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
        let tracked PermData { _access, _dealloc } = self._tokens.borrow_mut().tracked_pop();
        let node = ptr_mut_read(self.tail, Tracked(&mut _access));

        deallocate(
            self.tail as _,
            size_of::<LNode<T>>(),
            align_of::<LNode<T>>(),
            Tracked(_access.into_raw()),
            Tracked(_dealloc)
        );

        self.tail = node.prev;

        if self.tail as usize == 0 {
            assume(old(self)@.len() == 1);
            self.head = null_mut();
        }
        else {
            assert(old(self).wf_perm(old(self)@.len() - 2));
            let tracked PermData { _access, _dealloc } = self._tokens.borrow_mut().tracked_pop();
            let mut prev = ptr_mut_read(self.tail, Tracked(&mut _access));
            prev.next = null_mut();
            ptr_mut_write(self.tail, Tracked(&mut _access), prev);
            let tracked _ = self._tokens.borrow_mut().tracked_push(PermData { _access, _dealloc });

            assert forall |i: int| 0 <= i < self._tokens@.len()
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
            let tracked perm = self._tokens.borrow().tracked_borrow(self._tokens@.len() - 1);
            Some(&ptr_ref::<LNode<T>>(self.tail as _, Tracked(&perm._access)).value)
        }
    }

}

} // verus!

