pub mod fast_bit_set {
    use std::cell::Cell;
    use std::collections::BitvSet;
    use std::iter::AdditiveIterator;
    use std::fmt;
    use std::mem;
    use std::num::{Int, UnsignedInt};
    use std::raw::Repr;
    use std::raw::Slice as RawSlice;
    use std::{u8, uint};

    // `bit_exp`: an exponent such that `2^bit_exp` == `bits_per_elem`.
    // `bits_per_elem` must divide `T`'s size in bits by a power of 2.
    // Also, `T`'s preferred alignment must divide `T`'s size by a power of 2
    // The above requirements makes things nice and regular so we don't have to worry about
    // edge cases (hopefully).
    macro_rules! fast_bit_set(($storage:ident, $set:ident, $bit_exp:expr) => {

    // Can assume:
    //  sets * cells does not overflow
    //  mem::size_of::<T> << 3 does not overflow
    //  mem::size_of::<T> = 2^(k+bit_exp-3) for some k >= 0
    //  mem::size_of::<T> = 2^k * mem::align_of::<T> for some k >= 0
    //  mem::align_of::<T> = 2^k for some k >= 0
    //  set_size != 0
    //  1u << (bit_exp) does not overflow
    pub struct $storage<T> {
        storage: Vec<Cell<T>>, // backing storage for sets
        sets: uint, // total number of sets
        cells: uint, // cached: total number of cells per set
        set_size: uint, // cached: total elements per set
    }

    impl<T> $storage<T>
    where T: BitAnd<T, T> + BitOr<T, T> + Copy + PartialEq + Not<T> + Shl<uint, T> + Shr<uint, T> {
        /// `sets`: total number of sets to allocate storage for
        ///
        /// `set_size`: maximum number of elements per set (nonresizable)
        ///
        ///
        /// `initial`: the initial element (`std::mem::uninitialized()` is acceptable)
        pub fn new(sets: uint,
                   set_size: uint, elem: T) -> Option<$storage<T>> {
            // This whole function is checked really carefully to ensure that we get sane / defined
            // results in subsequent function calls.
            let cell_size = mem::size_of::<T>();
            let cell_align = mem::align_of::<T>();
            let cell_bits = match cell_size.checked_mul(u8::BITS) {
                Some(0) | None => return None, // Don't feel like dealing with it.
                Some(bits) => bits,
            };
            // Is there a saturating bit shift?
            if $bit_exp >= uint::BITS || !cell_bits.is_power_of_two() ||
               !cell_align.is_power_of_two() || set_size == 0 {
                // Don't feel like handling these, sorry
                return None
            }
            let bits_per_elem = 1 << $bit_exp;
            // Make sure cell size is bits_per_elem * 2^k where k >= 0
            let size_mask = bits_per_elem - 1;
            let align_mask = cell_align - 1;
            if cell_bits & size_mask != 0 || cell_size & align_mask != 0 {
                // Maybe could relax the restriction that bits_per_elem is 2^k * 2^bit_exp, but no
                // reason to right now.
                return None
            }
            let cells = (match set_size.checked_mul(bits_per_elem) {
                Some(bits) => bits,
                None => return None
            } - 1) / cell_bits + 1;
            sets.checked_mul(cells).map( |size| $storage {
                storage: Vec::from_elem(size, Cell::new(elem)),
                set_size: set_size,
                sets: sets,
                cells: cells,
            })
        }

        pub fn index<'a>(&self, index: uint) -> $set<'a, T> {
            assert!(index < self.sets);
            unsafe {
                $set {
                    storage: mem::transmute(RawSlice {
                        data: self.storage.as_ptr().offset((index * self.cells) as int),
                        len: self.cells,
                    }),
                }
            }
        }

        pub fn to_bitv_sets(&self) -> Vec<BitvSet> {
            let cell_size = mem::size_of::<T>();
            let cell_bits = cell_size << 3;
            let zero = unsafe { mem::zeroed::<T>() };
            let cell_exp = cell_size.trailing_zeros();
            let index_exp = cell_exp + 3 - $bit_exp;
            const ELEM_EXP: uint = 1 << $bit_exp;
            self.storage.chunks(self.cells).map( |cells| {
                let mut set = BitvSet::with_capacity(self.cells);
                for (index, &cell) in cells.iter().enumerate() {
                    // Hopefully this will get evaluated at compile time.  This is intended to
                    // avoid undefined behavior from overlong shifts without causing runtime
                    // overhead and is the primary reason we are using a macro at all.
                    if cell_bits == ELEM_EXP {
                        if cell.get() != zero {
                            set.insert(index);
                        }
                    } else {
                        let elem_mask = !zero >> (cell_bits - ELEM_EXP);
                        let mut cell = cell.get();
                        for index in range(index << index_exp, (index + 1) << index_exp) {
                            let flag = cell & elem_mask;
                            if flag != zero {
                                set.insert(index);
                            }
                            cell = cell >> ELEM_EXP;
                        }
                    }
                }
                set
            }).collect()
        }
    }

    impl<'a, T> fmt::Show for $storage<T>
    where T: BitAnd<T, T> + BitOr<T, T> + Copy + PartialEq + Not<T> + Shl<uint, T> + Shr<uint, T> {
        fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
            write!(f, "{}", self.to_bitv_sets())
        }
    }

    pub struct $set<'a, T: 'a> {
        storage: &'a [Cell<T>], // Might make this faster / save space by not including length
    }

    impl<'a, T> $set<'a, T>
    where T: BitAnd<T, T> + BitOr<T, T> + Copy + PartialEq + Not<T> + Shl<uint, T> + Shr<uint, T> + fmt::Show + Int {
        #[inline(always)]
        fn action<F>(&self, elem: uint, action: F) -> bool where F: FnOnce(*const Cell<T>, T) -> bool {
            let cell_size = mem::size_of::<T>();
            let cell_bits = cell_size << 3;
            let zero = unsafe { mem::zeroed::<T>() };
            let cell_exp = cell_size.trailing_zeros();
            let index_exp = cell_exp + 3 - $bit_exp;
            const ELEM_EXP: uint = 1 << $bit_exp;
            let index = elem >> index_exp;
            if index >= self.storage.len() { return false }
            let mask = if cell_bits == ELEM_EXP {
                !zero
            } else {
                let index_mask = (1 << index_exp) - 1;
                let subindex = elem & index_mask;
                let elem_mask = !zero >> (cell_bits - ELEM_EXP);
                elem_mask << (subindex << $bit_exp)
            };
            unsafe {
                let cell = self.storage.as_ptr().offset(index as int);
                action(cell, mask)
            }
        }

        #[inline]
        pub fn contains(&self, elem: uint) -> bool {
            self.action(elem, |: cell: *const Cell<T>, mask| unsafe {
                let cell_ = (*cell).get();
                let success = cell_ & mask != mem::zeroed();
                success
            })
        }

        #[inline]
        pub fn insert(&self, elem: uint) -> bool {
            self.action(elem, |: cell: *const Cell<T>, mask| unsafe {
                let cell_ = (*cell).get();
                let success = cell_ & mask == mem::zeroed();
                (*cell).set(cell_ | mask);
                success
            })
        }

        #[inline]
        pub fn remove(&self, elem: uint) -> bool {
            self.action(elem, |: cell: *const Cell<T>, mask| unsafe {
                let cell_ = (*cell).get();
                let success = cell_ & mask != mem::zeroed();
                (*cell).set(cell_ & !mask);
                success
            })
        }

        /// Note that the union will affect both self and other if they alias.
        /// Fails if self has a lower length than other.
        #[inline]
        pub fn union_with(&self, other: &$set<T>) {
            // Might just assume this and make this unsafe
            let RawSlice { data: mut theirs, len } = other.storage.repr();
            assert!(self.storage.len() >= len);
            let mut ours = self.storage.as_ptr();
            unsafe {
                let end = theirs.offset(len as int);
                while theirs != end {
                    let o = (*ours).get();
                    let t = (*theirs).get();
                    (*ours).set(o | t);
                    ours = ours.offset(1);
                    theirs = theirs.offset(1);
                }
            };
        }

        #[inline]
        pub fn len(&self) -> uint {
            if $bit_exp == 0u {
                self.storage.iter().map( |cell| cell.get().count_ones() ).sum()
            } else {
                let cell_size = mem::size_of::<T>();
                let cell_bits = cell_size << 3;
                let zero = unsafe { mem::zeroed::<T>() };
                let cell_exp = cell_size.trailing_zeros();
                let index_exp = cell_exp + 3 - $bit_exp;
                const ELEM_EXP: uint = 1 << $bit_exp;
                self.storage.iter().map( |cell| {
                    if cell_bits == ELEM_EXP {
                        if cell.get() != zero { 1 } else { 0 }
                    } else {
                        let elem_mask = !zero >> (cell_bits - ELEM_EXP);
                        let mut cell = cell.get();
                        let mut count = 0;
                        while cell != zero {
                            let flag = cell & elem_mask;
                            if flag != zero { count += 1 }
                            cell = cell >> ELEM_EXP;
                        }
                        count
                    }
                }).sum()
            }
        }
    }
    })

    fast_bit_set!(BitSetStorage, BitSet, 0)
    fast_bit_set!(ByteSetStorage, ByteSet, 3)
}


mod dirty_free_list {
    use arena::TypedArena;
    use std::cell::RefCell;

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
