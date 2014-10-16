use scanner as s;
use scanner::Tokens;

use arena::TypedArena;
use rustc::util::nodemap::{FnvHashMap, FnvHasher};
use std::cell::UnsafeCell;
use std::cmp;
use std::collections::hashmap;
use std::collections::hashmap::HashMap;
use std::mem;
use std::slice::BoxedSlice;

type ParseExpr<'a> = &'a [ParseTerm<'a>];

type ParseTerm<'a> = &'a [UnsafeCell<ParseFactor<'a>>];

enum ParseFactor<'a> {
    Ident(&'a [Ascii]),
    Lit(&'a [Ascii]),
    Opt(ParseExpr<'a>),
    Rep(ParseExpr<'a>),
    Group(ParseExpr<'a>),
}

enum ExprType {
    ProdEnd,
    OptEnd,
    RepEnd,
    GroupEnd,
}

pub struct ParserContext<'a> {
    factors: TypedArena<[UnsafeCell<ParseFactor<'a>>, .. STACK_VEC_MAX]>,
    vec_factors: TypedArena<UnsafeCell<Vec<UnsafeCell<ParseFactor<'a>>>>>,
    terms: TypedArena<[ParseTerm<'a>, .. STACK_VEC_MAX]>,
    vec_terms: TypedArena<UnsafeCell<Vec<ParseTerm<'a>>>>,
}

pub static MIN_PARSER_CONTEXT_CAPACITY: uint = 8;

impl<'a> ParserContext<'a> {
    pub fn new(capacity: uint) -> ParserContext<'a> {
        ParserContext {
            factors: TypedArena::with_capacity(cmp::max(MIN_PARSER_CONTEXT_CAPACITY, capacity)),
            vec_factors: TypedArena::with_capacity(cmp::max(MIN_PARSER_CONTEXT_CAPACITY, capacity >> 2)),
            terms: TypedArena::with_capacity(cmp::max(MIN_PARSER_CONTEXT_CAPACITY, capacity >> 4)),
            vec_terms: TypedArena::with_capacity(cmp::max(MIN_PARSER_CONTEXT_CAPACITY, capacity >> 6)),
        }
    }
}

// Parse context, holds information required by the parser (and owns any allocations it makes)
pub struct Parser<'a> {
    capacity: uint, // Guess at how many symbols to parse,
    stack: Vec<(StackVec<'a, ParseTerm<'a>>, StackVec<'a, UnsafeCell<ParseFactor<'a>>>, ExprType)> // Stored in the parse context so its allocation is reusable.
}

const STACK_VEC_MAX: uint = 4;

struct StackVec<'a, T> where T: 'a {
    vec: &'a mut Vec<T>,
    len: uint,
    stk: [T, .. STACK_VEC_MAX],
}

impl<'a,T> StackVec<'a, T> where T: 'a {
    #[inline(always)]
    fn push<'b>(&'b mut self, value: T, arena: &'a TypedArena<UnsafeCell<Vec<T>>>) {
        const STACK_VEC_LAST: uint = STACK_VEC_MAX - 1;
        #[allow(dead_code)] const STACK_VEC_PENULTIMATE: uint = STACK_VEC_LAST - 1;
        match self.len {
            l @ 0 ... STACK_VEC_PENULTIMATE => {
                self.stk[l] = value;
                self.len += 1;
            },
            STACK_VEC_LAST => {
                self.stk[STACK_VEC_LAST] = value;
                let stk = mem::replace(&mut self.stk, unsafe { mem::uninitialized() });
                let vec_box: Box<[T]> = box stk;
                self.vec = unsafe { &mut *arena.alloc(UnsafeCell::new(vec_box.into_vec())).get() };
                self.len += 1;
            },
            _ => self.vec.push(value),
        }
    }

    #[inline(always)]
    fn into_slice(mut self, arena: &'a TypedArena<[T, .. STACK_VEC_MAX]>) -> Option<&'a [T]> {
        match self.len {
            0 => None,
            STACK_VEC_MAX => {
                let vec = mem::replace(&mut self.vec, unsafe { mem::uninitialized() });
                Some(vec.as_slice())
            },
            l => {
                let stk = mem::replace(&mut self.stk, unsafe { mem::uninitialized() });
                Some(arena.alloc(stk).as_slice()[ .. l])
            },
        }
    }
}


macro_rules! parse_factor {
    ($tokens:expr, $ctx:expr, $stack:expr, $terms:expr, $factors:expr, $term: expr, $expr_lifetime:expr, $($term_token:pat => $term_lifetime:stmt)|*) => {{
        match $tokens.next() {
            s::Ident(i) =>$factors.push(UnsafeCell::new(Ident(i)), &$ctx.vec_factors),
            s::Lit(l) => $factors.push(UnsafeCell::new(Lit(l)), &$ctx.vec_factors),
            s::LBracket => {
                $stack.push(($terms, $factors, $term));
                $term = OptEnd;
                $expr_lifetime
            },
            s::LBrace => {
                $stack.push(($terms, $factors, $term));
                $term = RepEnd;
                $expr_lifetime
            },
            s::LParen => {
                $stack.push(($terms, $factors, $term));
                $term = GroupEnd;
                $expr_lifetime
            },
            s::UnterminatedStringLiteral => return Err(::UnterminatedStringLiteral),
            $(
                $term_token => { $term_lifetime }
            )*
            _ => return Err(::ExpectedFactorOrEnd),
        }
    }
}}

macro_rules! parse_terms {
    ($tokens:expr, $ctx: expr, $stack:expr, $terms:expr, $factors:expr, $term:expr, $expr_type:expr, $term_token:pat, $term_lifetime:expr, $cont_lifetime:expr) => {{
        'term: loop {
            // Parse first factor
            if $factors.len == 0 {
                parse_factor!($tokens, $ctx, $stack, $terms, $factors, $term, $cont_lifetime, );
            }
            'factor: loop {
                // Parse next factor OR VBar => end term OR terminal => end expression
                parse_factor!($tokens, $ctx, $stack, $terms, $factors, $term, $cont_lifetime, s::VBar => { break 'factor } | $term_token => { break 'term });
            }
            $terms.push($factors.into_slice(&$ctx.factors).unwrap(), &$ctx.vec_terms);
            $factors = mem::uninitialized();
            $factors.len = 0;
        }
        match $stack.pop() {
            Some((ts, fs, t)) => {
                $terms.push($factors.into_slice(&$ctx.factors).unwrap(), &$ctx.vec_terms);
                $factors = fs;
                $factors.push(UnsafeCell::new($expr_type($terms.into_slice(&$ctx.terms).unwrap())), &$ctx.vec_factors);
                $terms = ts;
                $term = t;
            }, None => { $term_lifetime }
        }
    }}
}

macro_rules! parse_expression {
    ($tokens:expr, $ctx:expr, $stack:expr) => {{
        let mut term = ProdEnd;
        let mut terms: StackVec<ParseTerm>;
        let mut factors: StackVec<UnsafeCell<ParseFactor>>;
        'expr: loop {
            unsafe {
                terms = mem::uninitialized();
                factors = mem::uninitialized();
                terms.len = 0;
                factors.len = 0;
                loop {
                    match term {
                        ProdEnd => parse_terms!($tokens, $ctx, $stack, terms, factors, term, (|_| unreachable!()), s::Semi, break 'expr, continue 'expr),
                        OptEnd => parse_terms!($tokens, $ctx, $stack, terms, factors, term, Opt, s::RBracket, break 'expr, continue 'expr),
                        RepEnd => parse_terms!($tokens, $ctx, $stack, terms, factors, term, Rep, s::RBrace, break 'expr, continue 'expr),
                        GroupEnd => parse_terms!($tokens, $ctx, $stack, terms, factors, term, Group, s::RParen, break 'expr, continue 'expr),
                    }
                }
            }
        }
        terms.push(factors.into_slice(&$ctx.factors).unwrap()/*[][ .. ])*/, &$ctx.vec_terms);
        terms.into_slice(&$ctx.terms).unwrap()/*[][ .. ];*/
    }}
}

impl<'a> Parser<'a> {
    // Create a new parse context from a given string
    pub fn new() -> Parser<'a> {
        Parser::with_capacity(hashmap::INITIAL_CAPACITY)
    }

    pub fn with_capacity(capacity: uint) -> Parser<'a> {
        Parser { stack: Vec::new(), capacity: capacity }
    }

    fn lock<'b, 'c>(&'c mut self) -> ParserGuard<'a, 'b, 'c> {
        unsafe {
            ParserGuard {
                inner_: mem::transmute(self),
                marker_: ::std::kinds::marker::CovariantLifetime,
            }
        }
    }

    // Deserialize a Ebnf.
    pub fn parse<'b, 'c>(&'c mut self,
                     ctx: &'b ParserContext<'b>,
                     string: &'b [Ascii]) -> Result<::Ebnf<'b>, ::Error> {
        let mut guard = self.lock();
        let guard = guard.deref_mut();
        let Parser { ref mut stack , capacity } = *guard;
        let mut tokens = Tokens::new(string);
        let (title, next) = match tokens.next() {
            s::Lit(title) => { (Some(title), tokens.next()) },
            s::UnterminatedStringLiteral => return Err(::UnterminatedStringLiteral),
            next => (None, next)
        };
        if next != s::LBrace { return Err(::ExpectedLBrace) }

        let mut productions: FnvHashMap<&[Ascii], ParseExpr> = HashMap::with_capacity_and_hasher(capacity, FnvHasher);
        loop {
            match tokens.next() {
                s::Ident(id) => {
                    if tokens.next() != s::Equals { return Err(::ExpectedEquals) }
                    match productions.entry(id) {
                        hashmap::Vacant(entry) => { entry.set(parse_expression!(tokens, ctx, stack)); }
                        hashmap::Occupied(_) => return Err(::DuplicateProduction),
                    }
                },
                s::RBrace => break,
                s::UnterminatedStringLiteral => return Err(::UnterminatedStringLiteral),
                _ => return Err(::ExpectedProduction),
            }
        }
        let (comment, next) = match tokens.next() {
            s::Lit(comment) => (Some(comment), tokens.next()),
            s::UnterminatedStringLiteral => return Err(::UnterminatedStringLiteral),
            next => (None, next),
        };
        match next {
            s::UnterminatedStringLiteral => return Err(::UnterminatedStringLiteral),
            s::EOF => Ok(::Ebnf { title: title, comment: comment, productions: {
                unsafe {
                    {
                        let mut piter = productions.iter().flat_map( |(_, &exp)|
                            exp.iter().flat_map( |t| t.iter() ) );
                        // Invariants: must read pfactors in order (never repeat a read), and must read
                        // them before they are written to (otherwise, we could accidentally ready a
                        // factor masquerading as a pfactor).  The reason this hack is necessary is
                        // that Rust lacks union types, or any other way of specifying that either a
                        // PFactor or a Factor may live in the same memory without tagging it.  The
                        // reason we don't want to tag it (or just keep an extra variant around) is for
                        // type safety: once the parsing phase is over we should only have Refs, never
                        // Idents.
                        for pfactor in piter {
                            let factor = match *pfactor.get() {
                                Ident(i) => match productions.find(&i) {
                                    Some(&e) => ::Ref(mem::transmute(e)),
                                    None => {println!("{}", i); return Err(::MissingProduction) }
                                },
                                Lit(l) => ::Lit(l),
                                Opt(e) => ::Opt(mem::transmute(e)),
                                Rep(e) => ::Rep(mem::transmute(e)),
                                Group(e) => ::Group(mem::transmute(e)),
                            };
                            *pfactor.get() = mem::transmute(factor)
                        }
                    }
                    mem::transmute(productions)
                }
            }}),
            _ => Err(::ExpectedEOF),
        }
    }
}

struct ParserGuard<'a, 'b: 'c, 'c> {
    marker_: ::std::kinds::marker::CovariantLifetime<'a>,
    inner_: &'c mut Parser<'b>
}

#[unsafe_destructor]
impl<'a, 'b, 'c> Drop for ParserGuard<'a, 'b, 'c> {
    fn drop(&mut self) {
        self.inner_.stack.clear();
    }
}

impl<'a, 'b, 'c> Deref<Parser<'b>> for ParserGuard<'a, 'b, 'c> {
    fn deref(&self) -> &Parser<'b> { self.inner_ }
}

impl<'a, 'b, 'c> DerefMut<Parser<'b>> for ParserGuard<'a, 'b, 'c> {
    fn deref_mut(&mut self) -> &mut Parser<'b> { self.inner_ }
}
