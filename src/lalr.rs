use Factor as F;
use self::fast_bit_set::{FastBitSet, FastBitSetStorage};

use std::cell::RefCell;
use std::collections::{hash_map, trie_map, BitvSet, HashMap, HashSet, RingBuf, VecMap};

struct Table<T> {
    table: T,
}

struct Row<A, G> {
    action: A,
    goto: G,
}

enum Action<S, R> {
    Shift(S),
    Reduce(R),
    Done,
}

trait Rule<E, N> {}

const EPSILON: uint = 0;

mod fast_bit_set {
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

pub fn first<'a>(ebnf: &::Ebnf<'a>) -> Option<FastBitSetStorage> {
    // http://david.tribble.com/text/lrk_parsing.html

    // 1. Add all of the nonterminals of the grammar to the nonterminals queue;
    let mut queue = range(0, ebnf.productions.len()).collect::<RingBuf<_>>();
    let first = match FastBitSetStorage::new(ebnf.productions.len(), ebnf.terminals.len()) {
        Some(first) => first,
        None => return None
    };
    // TODO: Error here if there were duplicate production entries, or something.

    loop {
        // 2. Pop nonterminal X from the head of the queue
        let xh = match queue.pop_front() { Some(xh) => xh, None => break };
        let mut x_first = first.index(xh);
        let mut x_contains_epsilon = x_first.contains(EPSILON);
        let old_len = x_first.len(); // Initial length of first set.

        let x = ebnf.productions[xh].1;
        // Compute a partial first(X) set for X
        for t in x.iter() { // For all rules with X as a LHS symbol
            let mut fs = t.iter();
            loop {
                match fs.next().map( |&f| f) {
                    None => { // X : epsilon
                        // 3. Add epsilon to first(X)
                        x_first.insert(EPSILON);
                        break
                    },
                    Some(F::Lit(EPSILON, _)) => continue, // Epsilon terminals are ignored
                    Some(F::Lit(t, _)) => { // X : t B ... with terminal symbol t as the leftmost RHS symbol
                        // 4. Add symbol t to first(X)
                        x_first.insert(t);
                        // Always break here, because we don't have a production so its first set
                        // cannot contain epsilon.
                        break;
                    },
                    Some(F::Ref(ph)) => { // X : P B ... with nonterminal symbol P
                        if ph != xh {
                            // add to first(X) all terminal symbols other than epsilon
                            // that are currently in first(P).
                            // (first(P) may still be incomplete at this point.)
                            let p_first = first.index(ph);
                            let contains_epsilon = p_first.contains(EPSILON);
                            x_first.union_with(&p_first);
                            // Repeat only if first(p) contains epsilon
                            if !contains_epsilon { break }
                            if !x_contains_epsilon { x_first.remove(EPSILON); }
                        }
                    },
                    Some(F::Opt(ph)) | Some(F::Rep(ph)) => { // X : [P] B, P != X
                        // add to first(X) all terminal symbols other than epsilon
                        // that are currently in first(P).
                        let p_first = first.index(ph);
                        p_first.insert(EPSILON);
                        x_first.union_with(&p_first);
                        if !x_contains_epsilon { x_first.remove(EPSILON); }
                        // Because first(p) contains epsilon, we always continue here.
                    },
                    Some(F::Group(ph)) => { // X : (P) B, P != X
                        // add to first(X) all terminal symbols other than epsilon
                        // that are currently in first(P).
                        let p_first = first.index(ph);
                        let contains_epsilon = p_first.contains(EPSILON);
                        x_first.union_with(&p_first);
                        // Repeat only if first(p) contains epsilon
                        if !contains_epsilon { break }
                        if !x_contains_epsilon { x_first.remove(EPSILON); }
                    },
                }
            }
            if old_len != x_first.len() || old_len == 0 {
                // If any terminals were added to first(X) in steps (3) through (6)
                // that were not already members of first(X),
                // or if first(X) is still empty, append X to the tail of the queue.
                queue.push_back(xh);
                // Otherwise,
                // first(X) is complete
                // (and nonterminal X is no longer in the queue);
            }
        }
    }
    Some(first)
}

pub fn first_for<'a>(set: &FastBitSet, term: ::Term<'a>, lookahead: uint, ebnf: &::Ebnf<'a>, first: &FastBitSetStorage) {
    for &f in term.iter() {
        match f {
            F::Lit(EPSILON, _) => continue,
            F::Lit(t, _) => {
                set.insert(t);
                return
            },
            F::Ref(s) | F::Group(s) => {
                set.union_with(&first.index(s));
                if !set.remove(EPSILON) { return }
            },
            F::Opt(s) | F::Rep(s) => {
                set.union_with(&first.index(s));
                set.remove(EPSILON);
            }
        }
    }
    set.insert(lookahead);
}

enum Lookahead<'a> {
    End,
    Symbol(&'a Ascii),
}

/*struct Item<'a> {
    lhs: uint,
    term: ::ParseTerm<'a>,
    lookahead: Lookahead<'a>,
}*/


//+THIS method is the bottleneck for the entire program!

//+THIS algorithm can be replaced with a better algorithm which
//+ executes in O(2s) time and O((n+t)r) space, where s = this.m_size,
//+ r = Grammar.m_nRules, n = Grammar.m_nNonterms, t = Grammar.m_nTerms;
//+
//+Algorithm:
//+ // initialize
//+ init ruleTable,
//+   each ruleTable[rI][s] represents closure item [rI. B -> . X Y, s];
//+   for each ruleTable[rI],
//+     ruleTable[rI] = null;
//+ mark1 += 2, mark2 += 2;
//+ if mark2 > BYTE_MAX,
//+   reset the ruleTable, and mark1 = 0, mark2 = 1;
//+ // generate closures for kernel items
//+ for each kernel item in this set, [rN. A -> B . S T, u],
//+   if ruleTable[rN] is null,
//+     ruleTable[rN] = allocate symbol table, byte array[n+t];
//+   // generate closure items from the kernel item
//+   for each rule rG with S as LHS (rule group for S), [rG. S -> X Y],
//+     for each symbol A in first(S T u),
//+       set ruleTable[rG][A] = mark1;
//+   end for;
//+ end for;
//+ // generate closures for non-kernel closure items
//+ do
//+   for each rule rI where ruleTable[rI] not null,
//+     for each symbol S in ruleTable[rI],
//+       if ruleTable[rI][S] == mark1,
//+         // generate closure items from [rI. B -> . X Y, S],
//+         for each rule rG with X as LHS (rule group for X),
//+           if ruleTable[rG][X] != mark2,
//+             set ruleTable[rG][X] = mark1;
//+         set ruleTable[rI][S] = mark2;
//+         didWork = true;
//+       end if;
//+     end for;
//+   end for;
//+ while didWork;
//+ // convert ruleTable entries into closure items
//+ for each rule rI where ruleTable[rI] not null,
//+   for each symbol S in ruleTable[rI],
//+     if ruleTable[rI][S] == mark1|mark2,
//+       create closure item, [rI. B -> . X Y, S];
//+       add item to this set;
//+     end if;
//+   end for;
//+ end for;
//+ // clean up
//+ for each ruleTable[rI],
//+   deallocate (recache) ruleTable[rI];
//+ end.
//pub fn generate_

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

impl<R> Table<VecMap<Row<VecMap<Action<uint, R>>, VecMap<uint>>>>
    where R: Rule<uint, uint>,
{
    type T = VecMap<Row<VecMap<Action<uint, R>>, VecMap<uint>>>;
    type Actions = VecMap<Action<uint, R>>;
    type Gotos = VecMap<uint>;
}

#[cfg(test)]
mod tests {
    use lalr;
    use lalr::fast_bit_set::FastBitSetStorage;
    use parser::{Parser, ParserContext};
    use std::hash::sip::{SipHasher, SipState};
    use test::Bencher;

    const EBNF_EBNF_STRING: &'static [u8] = include_bin!("resources/ebnf.ebnf");

    const ONE_LINE_EBNF_STRING: &'static [u8] = include_bin!("resources/one_line.ebnf");

    const ASN1_EBNF_STRING: &'static [u8] = include_bin!("resources/asn1.ebnf");

    const PAREN_EXPR: &'static [u8] = include_bin!("resources/paren_expr.ebnf");

    #[test]
    pub fn first_set_t() {
        let mut parser = Parser::<SipHasher, SipState>::with_capacity(8).unwrap();
        let ctx = ParserContext::new(1024);
        let string = //EBNF_EBNF_STRING
                     ASN1_EBNF_STRING
                     //ONE_LINE_EBNF_STRING
                     //PAREN_EXPR
                     .to_ascii();
        let ebnf = parser.parse(&ctx, string).unwrap();
        println!("{}", ebnf);
        let first = lalr::first(&ebnf).unwrap();
        println!("{}", first);
    }

    #[test]
    pub fn first_for() {
        let mut parser = Parser::<SipHasher, SipState>::with_capacity(8).unwrap();
        let ctx = ParserContext::new(16);
        let string = //EBNF_EBNF_STRING
                     //ASN1_EBNF_STRING
                     //ONE_LINE_EBNF_STRING
                     PAREN_EXPR
                     .to_ascii();
        let ebnf = parser.parse(&ctx, string).unwrap();
        println!("{}", ebnf);
        let firsts = lalr::first(&ebnf).unwrap();
        println!("{}", firsts);
        let end = ebnf.terminals.len();
        let mut sets = FastBitSetStorage::new(1, ebnf.terminals.len()).unwrap();
        let mut set = sets.index(0);
        let first = lalr::first_for(&set, ebnf.productions[0].1[1][1 .. ], end, &ebnf, &firsts);
        // {1, 3, 4}
        println!("{}", first);
    }

    #[bench]
    pub fn first_set_b(b: &mut Bencher) {
        let mut parser = Parser::<SipHasher, SipState>::with_capacity(1024).unwrap();
        //let ctx = ParserContext::new(8);
        let string = //EBNF_EBNF_STRING
                     ASN1_EBNF_STRING
                     //ONE_LINE_EBNF_STRING
                     .to_ascii();
        b.iter(|| {
            let ref ctx = ParserContext::new(0x100);
            //let ref ctx = ParserContext::new(80);
            //let ref ctx = ParserContext::new(8);
            //let ref ctx = ParserContext::new(32);
            //for _ in range(0, 10i8) {
                let ebnf = parser.parse(ctx, string).unwrap();
                let first = lalr::first(&ebnf).unwrap();
            //}
        });
    }
}
