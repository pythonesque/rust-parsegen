use Error as E;
use Factor as F;
use scanner as s;
use scanner::Tokens;

use ascii::{Ascii, AsciiCast};
use arena::TypedArena;
//use rustc::util::nodemap::{FnvHasher, FnvState};
use std::cell::UnsafeCell;
use std::cmp;
use std::default::Default;
use std::collections::hash_map;
//use std::collections::{HashMap};
use std::hash::{Hasher, SipHasher};
use std::intrinsics;
use std::marker::ContravariantLifetime;
use std::mem;
use std::ops::{Deref, DerefMut};
use std::ptr;
use std::raw::Repr;
//use std::collections::PriorityQueue;

use self::ExprType::*;
use self::ParseFactor::*;

/*pub struct FnvHasherDefault(pub FnvHasher);

impl Default for FnvHasherDefault {
    #[inline(always)]
    fn default() -> FnvHasherDefault { FnvHasherDefault(FnvHasher) }
}


impl Hasher<FnvState> for FnvHasherDefault {
    #[inline(always)]
    fn hash<T>(&self, t: &T) -> u64 where T: Hash<FnvState> {
        self.0.hash(t)
    }
}*/

/*struct ParseProduction<'a>(&'a [Ascii], ParseExpr<'a>);

impl<'a> PartialEq for ParseProduction<'a> {
    fn eq(&self, other: &ParseProduction<'a>) -> bool {
        self.0.eq(&other.0)
    }
}

impl<'a> PartialOrd for ParseProduction<'a> {
    fn partial_cmp(&self, other: &ParseProduction<'a>) -> Option<Ordering> {
        self.0.partial_cmp(&other.0)
    }
}

impl<'a> Eq for ParseProduction<'a> {}

impl<'a> Ord for ParseProduction<'a> {
    fn cmp(&self, other: &ParseProduction<'a>) -> Ordering {
        self.0.cmp(&other.0)
    }
}*/

type ParseExpr<'a> = &'a [ParseTerm<'a>];

type ParseTerm<'a> = &'a [UnsafeCell<ParseFactor<'a>>];

enum ParseFactor<'a> {
    Ident(&'a [Ascii]),
    Lit(&'a [Ascii]),
    // Here be hacks: the length of the ParseExpr array is initially zero.  We do this because the
    // data in the pointer isn't initially valid.
    //
    // The reason this is important is that anonymous expressions live in the same location as the
    // identifier part of the (name, expr) pairs in our productions vector.  Before we sort, we
    // want to move all these to the end of the array (so we don't accidentally reference them
    // during the sort), which requires updating the pointer in the fields below.  These fields
    // will become inaccurate as the vector grows, so we also can't rely on their initial values to
    // be correct--instead, we point directly into them from the data pointer of the expr part of
    // the pair (it would normally be interpreted as a pointer into Ascii data, but in this case
    // the length will be zero so we're safe).
    //
    // To make this work, we rely on the scanner to never give us zero-length Idents.
    // We actually might still be able to support them since we could identify them by making the
    // data pointer of the slice 0 for such identifiers, but I don't want to think about it for
    // now.
    Opt(usize),
    Rep(usize),
    Group(usize),
}

#[derive(Show)]
enum ExprType {
    ProdEnd,
    OptEnd,
    RepEnd,
    GroupEnd,
}

pub struct ParserContext<'a> {
    factors: TypedArena<[UnsafeCell<ParseFactor<'a>> ; STACK_VEC_MAX]>,
    vec_factors: TypedArena<UnsafeCell<Vec<UnsafeCell<ParseFactor<'a>>>>>,
    terms: TypedArena<[ParseTerm<'a> ; STACK_VEC_MAX]>,
    vec_terms: TypedArena<UnsafeCell<Vec<ParseTerm<'a>>>>,
}

pub static MIN_PARSER_CONTEXT_CAPACITY: usize = 8;

impl<'a> ParserContext<'a> {
    pub fn new(capacity: usize) -> ParserContext<'a> {
        ParserContext {
            factors: TypedArena::with_capacity(cmp::max(MIN_PARSER_CONTEXT_CAPACITY, capacity)),
            vec_factors: TypedArena::with_capacity(cmp::max(MIN_PARSER_CONTEXT_CAPACITY, capacity >> 2)),
            terms: TypedArena::with_capacity(cmp::max(MIN_PARSER_CONTEXT_CAPACITY, capacity >> 4)),
            vec_terms: TypedArena::with_capacity(cmp::max(MIN_PARSER_CONTEXT_CAPACITY, capacity >> 6)),
        }
    }
}

// Parse context, holds information required by the parser (and owns any allocations it makes)
//pub struct Parser<'a, Hasher = XXHasher, State = XXState> {
//pub struct Parser<'a, Hasher = FnvHasherDefault, State = FnvState> {
pub struct Parser<'a, Hasher = SipHasher> {
    capacity: usize, // Guess at how many symbols to parse,
    stack: Vec<(StackVec<'a, ParseTerm<'a>>, StackVec<'a, UnsafeCell<ParseFactor<'a>>>, ExprType)>, // Stored in the parse context so its allocation is reusable.
    /*tx: Sender<Option<(&'static [Ascii], &'static [ParseTerm<'static>])>>,
    rx: Receiver<Option<Vec<(&'static [Ascii], &'static [ParseTerm<'static>])>>>,*/
    //seed: Hasher,
}

const STACK_VEC_MAX: usize = 4; // Arrived at by highly scientific guess and check algorithm

struct StackVec<'a, T> where T: 'a {
    marker: ContravariantLifetime<'a>,
    vec: *mut Vec<T>,
    len: usize,
    stk: [T ; STACK_VEC_MAX],
}

impl<'a,T> StackVec<'a, T> where T: 'a {
    #[inline(always)]
    fn push<'b>(&'b mut self, value: T, arena: &'a TypedArena<UnsafeCell<Vec<T>>>) {
        const STACK_VEC_LAST: usize = STACK_VEC_MAX - 1;
        const STACK_VEC_PENULTIMATE: usize = STACK_VEC_LAST - 1;
        match self.len {
            l @ 0 ... STACK_VEC_PENULTIMATE => {
                self.stk[l] = value;
                self.len += 1;
            },
            STACK_VEC_LAST => {
                self.stk[STACK_VEC_LAST] = value;
                let stk = mem::replace(&mut self.stk, unsafe { mem::uninitialized() });
                let vec_box: Box<[T]> = box stk;
                self.vec = unsafe { arena.alloc(UnsafeCell::new(vec_box.into_vec())).get() };
                self.len += 1;
            },
            _ => unsafe { (*self.vec).push(value) },
        }
    }

    #[inline(always)]
    fn into_slice(mut self, arena: &'a TypedArena<[T ; STACK_VEC_MAX]>) -> Option<&'a [T]> {
        match self.len {
            0 => None,
            STACK_VEC_MAX => {
                let vec = unsafe { mem::transmute::<_,&'a mut Vec<_>>(mem::replace(&mut self.vec, mem::uninitialized())) };
                Some(&vec[])
            },
            l => {
                let stk = mem::replace(&mut self.stk, unsafe { mem::uninitialized() });
                Some(&arena.alloc(stk)[][ .. l])
            },
        }
    }
}


macro_rules! parse_factor {
    ($tokens:expr, $ctx:expr, $terminals:expr, $count_terms:expr, $stack:expr, $terms:expr, $factors:expr, $term: expr, $expr_lifetime:expr, $($term_token:pat => $term_lifetime:stmt),*) => {{
        match $tokens.next() {
            s::Ident(i) =>$factors.push(UnsafeCell::new(Ident(i)), &$ctx.vec_factors),
            //s::Ident =>$factors.push(UnsafeCell::new(Ident($tokens.tok)), &$ctx.vec_factors),
            s::Lit(l) => {
                $terminals.push(l);
                $factors.push(UnsafeCell::new(Lit(l)), &$ctx.vec_factors);
            },
            //s::Lit => $factors.push(UnsafeCell::new(Lit($tokens.tok)), &$ctx.vec_factors),
            s::LBracket => {
                $stack.push(($terms, $factors, $term));
                $term = OptEnd;
                $count_terms += 1;
                $expr_lifetime
            },
            s::LBrace => {
                $stack.push(($terms, $factors, $term));
                $term = RepEnd;
                $count_terms += 1;
                $expr_lifetime
            },
            s::LParen => {
                $stack.push(($terms, $factors, $term));
                $term = GroupEnd;
                $expr_lifetime
            },
            s::UnterminatedStringLiteral => return Err(E::UnterminatedStringLiteral),
            $(
                $term_token => { $term_lifetime }
            ),*
            _ => return Err(E::ExpectedFactorOrEnd),
        }
    }
}}

static EMPTY_ASCII: [Ascii ; 0] = [];

macro_rules! parse_terms {
    ($tokens:expr, $ctx:expr, $productions:expr, $terminals:expr, $anon_factors:expr, $count_terms:expr, $stack:expr, $terms:expr, $factors:expr, $term:expr, $expr_type:expr, $term_token:pat, $term_lifetime:expr, $cont_lifetime:expr) => {{
        'term: loop {
            // Parse first factor
            $count_terms += 1;
            if $factors.len == 0 {
                parse_factor!($tokens, $ctx, $terminals, $count_terms, $stack, $terms, $factors, $term, $cont_lifetime, );
            }
            'factor: loop {
                // Parse next factor OR VBar => end term OR terminal => end expression
                parse_factor!($tokens, $ctx, $terminals, $count_terms, $stack, $terms, $factors, $term, $cont_lifetime, s::VBar => { break 'factor }, $term_token => { break 'term });
            }
            $terms.push($factors.into_slice(&$ctx.factors).unwrap(), &$ctx.vec_terms);
            $factors = StackVec {
                marker: ContravariantLifetime,
                len: 0,
                vec: mem::uninitialized(),
                stk: mem::transmute([Opt(1), Opt(1), Opt(1), Opt(1)]),
            };
            $factors.len = 0;
        }
        match $stack.pop() {
            Some((ts, fs, t)) => {
                $terms.push($factors.into_slice(&$ctx.factors).unwrap(), &$ctx.vec_terms);
                $factors = fs;
                $anon_factors += 1;
                $factors.push(UnsafeCell::new($expr_type($anon_factors)), &$ctx.vec_factors);
                $productions.push(UnsafeCell::new((
                    &EMPTY_ASCII[],
                    $terms.into_slice(&$ctx.terms).unwrap()
                )));
                $terms = ts;
                $term = t;
            }, None => { $term_lifetime }
        }
    }}
}

macro_rules! parse_expression {
    ($tokens:expr, $ctx:expr, $productions:expr, $terminals:expr, $anon_factors:expr, $count_terms:expr, $stack:expr) => {{
        let mut term = ProdEnd;
        let mut terms: StackVec<ParseTerm>;
        let mut factors: StackVec<UnsafeCell<ParseFactor>>;
        'expr: loop {
            unsafe {
                terms = StackVec {
                    marker: ContravariantLifetime,
                    len: 0,
                    vec: mem::uninitialized(),
                    stk: [mem::transmute((1us,1us)) ; STACK_VEC_MAX ],
                };
                factors = StackVec {
                    marker: ContravariantLifetime,
                    len: 0,
                    vec: mem::uninitialized(),
                    stk: mem::transmute([Opt(1), Opt(1), Opt(1), Opt(1)]),
                };
                terms.len = 0;
                factors.len = 0;
                loop {
                    match term {
                        ProdEnd => parse_terms!($tokens, $ctx, $productions, $terminals, $anon_factors, $count_terms, $stack, terms, factors, term, (|:_| intrinsics::unreachable()), s::Semi, break 'expr, continue 'expr),
                        OptEnd => parse_terms!($tokens, $ctx, $productions, $terminals, $anon_factors, $count_terms, $stack, terms, factors, term, Opt, s::RBracket, break 'expr, continue 'expr),
                        RepEnd => parse_terms!($tokens, $ctx, $productions, $terminals, $anon_factors, $count_terms, $stack, terms, factors, term, Rep, s::RBrace, break 'expr, continue 'expr),
                        GroupEnd => parse_terms!($tokens, $ctx, $productions, $terminals, $anon_factors, $count_terms, $stack, terms, factors, term, Group, s::RParen, break 'expr, continue 'expr),
                    }
                }
            }
        }
        terms.push(factors.into_slice(&$ctx.factors).unwrap()/*[][ .. ])*/, &$ctx.vec_terms);
        terms.into_slice(&$ctx.terms).unwrap()/*[][ .. ];*/
    }}
}

impl<'a, H> Parser<'a, H> where H: Default + Hasher {
    // Create a new parse context from a given string
    pub fn new() -> Result<Parser<'a, H>, ()> {
        Parser::with_capacity(hash_map::INITIAL_CAPACITY)
    }

    pub fn with_capacity(capacity: usize) -> Result<Parser<'a, H>, ()> {
        /*let (txmain, rxmain) = channel();
        let (txwork, rxwork) = channel();
        txmain.send(None);
        let worker: proc(): 'a = proc() {
            let (tx, rx) = (txwork, rxmain);
            let _ = rx.recv(); // Synchronize during parser initialization
            tx.send(None); // Start up the parser
            'b: loop {
                let mut productions = Vec::with_capacity(capacity); // new vector
                // Wait for parser run synchronization (Some(elem))
                for m in rx.iter().take_while( |m| m.is_none() ) {
                    tx.send(None); // Confirmation message was received.
                }
                // Begin parser run
                for m in rx.iter() {
                    match m {
                        Some(elem) => {
                            // Received an element--process it.
                            productions.push(elem);
                        }
                        None => {
                            // Send off the productions
                            match tx.send_opt(Some(unsafe { mem::transmute(productions) }))  {
                                Ok(()) => continue 'b, // Start over
                                Err(data) => {
                                    // Could be memory unsafety, leak and die
                                    unsafe { ::std::mem::forget(data) }
                                    break;
                                }
                            }
                        }
                    }
                }
                return; // Exit the thread
            }
        };
        unsafe {
            let worker: proc(): Send = mem::transmute(worker);
            spawn(worker);
        }
        try!(rxwork.recv_opt());*/
        Ok(Parser { stack: Vec::new(), capacity: capacity, /*seed: Default::default() /*tx: txmain, rx: rxwork*/*/ })
    }

    fn lock<'b, 'c>(&'c mut self) -> ParserGuard<'a, 'b, 'c> {
        let guard = unsafe {
            ParserGuard {
                inner_: mem::transmute(self),
                marker_: ::std::marker::CovariantLifetime,
            }
        };
        // Synchronize with worker
        /*guard.tx.send(None);
        'a: loop {
            for msg in guard.rx.iter() {
                match msg {
                    Some(data) => {
                        // This shouldn't actually happen, but let's be careful for now and
                        // leak rather than cause unsafety
                        unsafe { ::std::mem::forget(data) }
                    },
                    None => break 'a
                }
            }
            // Worker thread died, bail out.  ParserGuard will protect us.
            fail!("Worker thread died!")
        };*/
        guard
    }

    // Deserialize a Ebnf.
    pub fn parse<'b, 'c>(&'c mut self,
                     ctx: &'b ParserContext<'b>,
                     string: &'b [Ascii]) -> Result<::Ebnf<'b>, ::Error> {
        let mut guard = self.lock();
        let guard = guard.deref_mut();
        let Parser { ref mut stack , capacity, /*ref tx, ref rx, */ /*seed,*/ } = *guard;
        let mut tokens = Tokens::new(string);
        let (title, next) = match tokens.next() {
            //s::Lit => { (Some(tokens.tok), tokens.next()) },
            s::Lit(title) => { (Some(title), tokens.next()) },
            s::UnterminatedStringLiteral => return Err(E::UnterminatedStringLiteral),
            next => (None, next)
        };
        if next != s::LBrace { return Err(E::ExpectedLBrace) }
        //let mut productions: FnvHashMap<&[Ascii], ParseExpr> = HashMap::with_capacity_and_hasher(capacity, FnvHasher);
        //let mut productions: FnvHashMap<&[Ascii], ParseExpr> = HashMap::with_capacity_and_hasher(0, FnvHasher);
        //let mut productions: HashMap<&[Ascii], ParseExpr>;
        //let mut productions: HashMap<&[Ascii], ParseExpr, FnvHasherDefault>;
        //let mut productions: HashMap<&[Ascii], ParseExpr, FnvHasherDefault> = HashMap::with_capacity_and_hasher(capacity, FnvHasherDefault(FnvHasher));
        //let mut productions: HashMap<&[Ascii], ParseExpr, FnvHasherDefault> = HashMap::with_capacity_and_hasher(capacity, FnvHasherDefault(FnvHasher));
        //let mut productions/*: HashMap<&[Ascii], ParseExpr, H>*/ = HashMap::with_capacity_and_hasher(capacity, /*::new_with_seed(0)*/ seed);
        //let mut productions = BTreeMap::with_b(23);
        let mut productions_ = Vec::with_capacity(capacity);
        //let mut productions_ = PriorityQueue::with_capacity(capacity);
        let mut terminals = Vec::with_capacity(capacity);
        let (mut anon_factors, mut count_terms) = (0, 0);
        loop {
            match tokens.next() {
                /*s::Ident => {
                    let id = tokens.tok;*/
                s::Ident(id) => {
                    if tokens.next() != s::Equals { return Err(E::ExpectedEquals) }
                    //if !tokens.consume_equals() { return Err(::ExpectedEquals) }
                    /*match productions.entry(id) {
                        //btree::Vacant(entry) => { entry.set(parse_expression!(tokens, ctx, stack)); }
                        //btree::Occupied(_) => return Err(::DuplicateProduction),
                        hash_map::Vacant(entry) => { entry.set(parse_expression!(tokens, ctx, stack)); }
                        hash_map::Occupied(_) => return Err(::DuplicateProduction),
                    }*/
                    //productions_.push((id, parse_expression!(tokens, ctx, stack)));
                    //productions_.push(/*ParseProduction*/UnsafeCell::new((id, parse_expression!(tokens, ctx, productions_, anon_factors, stack))));
                    let e = parse_expression!(tokens, ctx, productions_, terminals, anon_factors, count_terms, stack);
                    productions_.push(UnsafeCell::new((id, e)));
                    // Should be protected by the ParserGuard so don't worry about failing here.
                    //tx.send(unsafe { mem::transmute(Some((id, parse_expression!(tokens, ctx, stack)))) })
                },
                s::RBrace => break,
                s::UnterminatedStringLiteral => return Err(E::UnterminatedStringLiteral),
                _ => return Err(E::ExpectedProduction),
            }
        }
        let (comment, next) = match tokens.next() {
            //s::Lit => (Some(tokens.tok), tokens.next()),
            s::Lit(comment) => (Some(comment), tokens.next()),
            s::UnterminatedStringLiteral => return Err(E::UnterminatedStringLiteral),
            next => (None, next),
        };
        match next {
            s::UnterminatedStringLiteral => return Err(E::UnterminatedStringLiteral),
            s::EOF => {
                terminals.reserve_exact(1);
                terminals.push(&EMPTY_ASCII); // Should always sort to element zero
                terminals.as_mut_slice().sort();
                terminals.dedup();
                //tx.send(None); // We're done!
                //productions_ = rx.recv().unwrap(); // If it's not Some(x) that's a logic bug.
                let mut productions = unsafe {
                    let mut first = productions_.as_ptr();
                    let mut last = first.offset(productions_.len() as isize);
                    let mut first_inner = ptr::read((&*first).get() as *const (&[Ascii], ParseExpr));
                    while first != last {
                        if first_inner.0.len() == 0 {
                            // This is an unnamed production.  Swap it with the last production and
                            // decrement.
                            last = last.offset(-1);
                            let last_inner = ptr::read((&*last).get() as *const _);
                            *((*last).get() as *mut _) = first_inner;
                            first_inner = last_inner;
                        } else {
                            *((*first).get() as *mut _) = first_inner;
                            first = first.offset(1);
                            first_inner = ptr::read((&*first).get() as *const _);
                        }
                    }
                    mem::transmute::<_, Vec<(&[Ascii], ParseExpr)>>(productions_)
                };
                let len = productions.len();
                productions[.. len - anon_factors].sort_by( |a, b| a.0.cmp(b.0) );
                let productions_ = productions;
                let productions = productions_[].repr();
                // In general, we shouldn't be able to fail for this section.
                let mut error = Ok::<_, ::Error>(());
                let productions = unsafe {
                    let productions = mem::transmute::<_, &[(&[Ascii], ParseExpr)]>(productions);
                    let search_productions = &productions[0 .. productions.len() - anon_factors ];
                    let mut last_tag = &EMPTY_ASCII[];
                    let mut count = len - anon_factors;
                    productions_.map_in_place( |(tag, pexp)| {
                        if count != 0 {
                            if last_tag == tag { error = Err(E::DuplicateProduction) }
                            last_tag = tag;
                            count -= 1;
                        }
                        // Invariants: must read pfactors in order (never repeat a read), and must read
                        // them before they are written to (otherwise, we could accidentally ready a
                        // factor masquerading as a pfactor).  The reason this hack is necessary is
                        // that Rust lacks union types, or any other way of specifying that either a
                        // PFactor or a Factor may live in the same memory without tagging it.  The
                        // reason we don't want to tag it (or just keep an extra variant around) is for
                        // type safety: once the parsing phase is over we should only have Refs, never
                        // Idents.
                        for t in pexp.iter() {
                            for pfactor in t.iter() {
                                let factor = match *pfactor.get() {
                                    Ident(i) => F::Ref(match
                                        search_productions.binary_search_by(|&(id, _)| id.cmp(i)) {
                                        Ok(id) => id,
                                        _ => {
                                            // Acknowledge the error and continue (can't exit).
                                            error = Err(E::MissingProduction);
                                            0
                                        }
                                    }),
                                    Lit(l) => F::Lit(match terminals.binary_search(&l) {
                                        Ok(id) => id,
                                        _ => intrinsics::unreachable()
                                    }, 0),
                                    Opt(id) => F::Opt(len - id),
                                    Rep(id) => F::Rep(len - id),
                                    Group(id) => F::Group(len - id),
                                };
                                *(pfactor.get() as *mut _) = factor;
                            }
                        }
                        mem::transmute((tag, pexp))
                    })
                };
                error.and(Ok(::Ebnf {
                    title: title,
                    comment: comment,
                    terminals: terminals,
                    n_terms: count_terms,
                    productions: productions
                }))
            },
            _ => Err(E::ExpectedEOF),
        }
    }
}

struct ParserGuard<'a, 'b: 'c, 'c> {
    marker_: ::std::marker::CovariantLifetime<'a>,
    inner_: &'c mut Parser<'b>
}

#[unsafe_destructor]
impl<'a, 'b, 'c> Drop for ParserGuard<'a, 'b, 'c> {
    fn drop(&mut self) {
        self.inner_.stack.clear();
        /*self.tx.send(None);
        self.rx.recv(); // If this fails we abort in order to preserve memory safety.*/
    }
}

impl<'a, 'b, 'c> Deref for ParserGuard<'a, 'b, 'c> {
    type Target = Parser<'b>;
    fn deref(&self) -> &Parser<'b> { self.inner_ }
}

impl<'a, 'b, 'c> DerefMut for ParserGuard<'a, 'b, 'c> {
    fn deref_mut(&mut self) -> &mut Parser<'b> { self.inner_ }
}
