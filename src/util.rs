pub mod fast_bit_set {
    use std::cell::Cell;
    use std::collections::{bitv, BitvSet};
    use std::iter::AdditiveIterator;
    use std::kinds::marker;
    use std::fmt;
    use std::mem;
    use std::num::Int;
    use std::raw::Repr;
    use std::raw::Slice as RawSlice;
    use std::u32;

    pub struct FastBitSetStorage {
        storage: Vec<Cell<u32>>,
        sets: uint,
        cells: uint, // cached
        bits: uint,
    }

    impl FastBitSetStorage {
        pub fn new(sets: uint, bits: uint) -> Option<FastBitSetStorage> {
            if bits == 0 { return None } // Don't feel like handling this, sorry
            let cells = (bits - 1) / u32::BITS + 1;
            sets.checked_mul(cells).map( |size| FastBitSetStorage {
                storage: Vec::from_elem(size, Cell::new(0)),
                bits: bits,
                sets: sets,
                cells: cells,
            })
        }

        pub fn index<'a>(&self, index: uint) -> FastBitSet<'a> {
            assert!(index < self.sets);
            unsafe {
                FastBitSet {
                    storage: mem::transmute(RawSlice {
                        data: self.storage.as_ptr().offset((index * self.cells) as int),
                        len: self.cells,
                    }),
                }
            }
        }

        pub fn to_bitv_sets(&self) -> Vec<BitvSet> {
            self.storage.chunks(self.cells).map( |cells|
                BitvSet::from_bitv(bitv::from_fn(self.bits, |elem| unsafe {
                    assert!(elem < self.bits);
                    let index = elem >> 5;
                    let subindex = elem & 31;
                    let mask = 1u32 << subindex;
                    let cell = cells.as_ptr().offset(index as int);
                    let cell_ = (*cell).get();
                    cell_ & mask != 0
            }))).collect::<Vec<_>>()
        }
    }

    impl<'a> fmt::Show for FastBitSetStorage {
        fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
            write!(f, "{}", self.to_bitv_sets())
        }
    }

    pub struct FastBitSet<'a> {
        storage: &'a [Cell<u32>], // Might make this faster / save space by not including length
    }

    impl<'a> FastBitSet<'a> {
        #[inline]
        pub fn contains(&self, elem: uint) -> bool {
            let index = elem >> 5;
            let subindex = elem & 31;
            let mask = 1u32 << subindex;
            if index >= self.storage.len() { return false }
            unsafe {
                let cell = self.storage.as_ptr().offset(index as int);
                let cell_ = (*cell).get();
                let success = cell_ & mask != 0;
                success
            }
        }

        #[inline]
        pub fn insert(&self, elem: uint) -> bool {
            let index = elem >> 5;
            let subindex = elem & 31;
            let mask = 1u32 << subindex;
            if index >= self.storage.len() { return false }
            unsafe {
                let cell = self.storage.as_ptr().offset(index as int);
                let cell_ = (*cell).get();
                let success = cell_ & mask == 0;
                (*cell).set(cell_ | mask);
                success
            }
        }

        #[inline]
        pub fn remove(&self, elem: uint) -> bool {
            let index = elem >> 5;
            let subindex = elem & 31;
            let mask = 1u32 << subindex;
            if index >= self.storage.len() { return false }
            unsafe {
                let cell = self.storage.as_ptr().offset(index as int);
                let cell_ = (*cell).get();
                let success = cell_ & mask != 0;
                (*cell).set(cell_ & !mask);
                success
            }
        }

        /// Note that the union will affect both self and other if they alias.
        /// Fails if self has a lower length than other.
        #[inline]
        pub fn union_with(&self, other: &FastBitSet) {
            // Might just assume this and make this unsafe
            let RawSlice { data: mut ours, len } = self.storage.repr();
            assert!(len >= other.storage.len());
            let mut theirs = other.storage.as_ptr();
            unsafe {
                let end = theirs.offset(len as int);
                while theirs != end {
                    let s = (*ours).get();
                    let o = (*theirs).get();
                    (*ours).set(s | o);
                    ours = ours.offset(1);
                    theirs = theirs.offset(1);
                }
            }
        }

        #[inline]
        pub fn len(&self) -> uint {
            self.storage.iter().map( |cell| cell.get().count_ones() ).sum()
        }
    }
}


mod dirty_free_list {
    use arena::TypedArena;
    use std::cell::RefCell;
    use std::mem;

    /// A "dirty" free list that doesn't zero elements on destruction.
    pub struct FreeList<'a, T: 'a, F: 'a> where F: Fn() -> T {
        arena: TypedArena<Node<'a, T>>,
        first: RefCell<Option<&'a mut Node<'a, T>>>,
        alloc: F,
    }

    pub static FREE_LIST_DEFAULT_CAPACITY: uint = 8;

    impl<'a, T, F> FreeList<'a, T, F>  where F: Fn() -> T {
        pub fn new(alloc: F) -> FreeList<'a, T, F> {
            FreeList::with_capacity(FREE_LIST_DEFAULT_CAPACITY, alloc)
        }

        pub fn with_capacity(capacity: uint, alloc: F) -> FreeList<'a, T, F> {
            FreeList {
                arena: TypedArena::with_capacity(capacity),
                first: RefCell::new(None),
                alloc: alloc,
            }
        }

        fn alloc(&'a self) -> &'a mut Node<'a, T> {
            let mut first = self.first.borrow_mut();
            let first = first.deref_mut();
            let node = match first.take() {
                Some(first) => first,
                None => self.arena.alloc(Node { data: (self.alloc)(), next: None })
            };
            *first = node.next.take();
            node
        }

        /*fn iter<'b>(&'b self) -> FreeListItems<'a, 'b, T> {
            FreeListItems {
                node: Option<&mut Node<'a, T>>,
            }
        }*/
    }

    struct Node<'a, T: 'a> {
        data: T,
        next: Option<&'a mut Node<'a, T>>,
    }

    pub struct Hole<'a, T: 'a, F: 'a> where F: Fn() -> T {
        // Should always be Some, we do this to perform the Option dance.  May remove the Option
        // later if it turns out to be too slow.
        inner: Option<&'a mut Node<'a, T>>,
        // Not strictly necessary but ensures we avoid leaks and add this back to the old freelist
        // when we're done with it.  If this turns out to be too wasteful we can do the drops
        // explicitly and eliminate this member.
        free_list: &'a FreeList<'a, T, F>,
    }

    impl<'a, T, F> Hole<'a, T, F> where F: Fn() -> T {
        #[inline]
        pub fn new(free_list: &'a FreeList<'a, T, F>) -> Hole<'a, T, F> {
            Hole { inner: None, free_list: free_list }
        }

        /// This should not be able to panic
        #[inline]
        pub fn unwrap<'b>(&'b mut self) -> &'b mut T {
            match self.inner {
                Some(ref mut inner) => &mut inner.data,
                None => {
                    self.inner = Some(self.free_list.alloc());
                    &mut self.inner.as_mut().unwrap().data
                }
            }
        }

        #[inline]
        pub fn free<'b>(&'b mut self) {
            debug_assert!(self.inner.as_ref().unwrap().next.is_none()); // Doesn't cause memory unsafety but could leak 
            let mut first = self.free_list.first.borrow_mut();
            self.inner.as_mut().unwrap().next = first.take();
            *first = self.inner.take();
        }
    }

    #[unsafe_destructor]
    impl<'a, T, F> Drop for Hole<'a, T, F> where F: Fn() -> T {
        #[inline]
        fn drop<'b>(&'b mut self) {
            self.free();
        }
    }
}

// Cheap unwind
#[inline(never)] #[cold] // No bloat
pub fn fast_unwind<T>() -> T {
    panic!()
}
