use scanner as s;
use scanner::Tokens;

use arena::TypedArena;
use std::cell::UnsafeCell;
use std::collections::hashmap;
use rustc::util::nodemap::FnvHashMap;
use std::mem;

type ParseExpr<'a> = &'a [ParseTerm<'a>];

type ParseTerm<'a> = Vec<UnsafeCell<ParseFactor<'a>>>;

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
    arena: TypedArena<Vec<ParseTerm<'a>>>,
}

impl<'a> ParserContext<'a> {
    pub fn new() -> ParserContext<'a> {
        ParserContext {
            arena: TypedArena::new(),
        }
    }
}

// Parse context, holds information required by the parser (and owns any allocations it makes)
pub struct Parser<'a> {
    stack: Vec<(Vec<ParseTerm<'a>>, ParseTerm<'a>, ExprType)> // Stored in the parse context so its allocation is reusable.
}

macro_rules! parse_factor {
    ($tokens:expr, $stack:expr, $terms:expr, $factors:expr, $term: expr, $expr_lifetime:expr, $($term_token:pat => $term_lifetime:stmt)|*) => {
        match $tokens.next() {
            s::Ident(i) => $factors.push(UnsafeCell::new(Ident(i))),
            s::Lit(l) => $factors.push(UnsafeCell::new(Lit(l))),
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
}

macro_rules! parse_terms {
    ($tokens:expr, $arena: expr, $stack:expr, $terms:expr, $factors:expr, $term:expr, $expr_type:expr, $term_token:pat, $term_lifetime:expr, $cont_lifetime:expr) => {{
        'term: loop {
            // Parse first factor
            if $factors.is_empty() {
                parse_factor!($tokens, $stack, $terms, $factors, $term, $cont_lifetime, );
            }
            'factor: loop {
                // Parse next factor OR VBar => end term OR terminal => end expression
                parse_factor!($tokens, $stack, $terms, $factors, $term, $cont_lifetime, s::VBar => { break 'factor } | $term_token => { break 'term });
            }
            $terms.push($factors);
            $factors = Vec::new();
        }
        match $stack.pop() {
            Some((ts, fs, t)) => {
                $terms.push($factors);
                $factors = fs;
                $factors.push(UnsafeCell::new($expr_type($arena.alloc($terms)[])));
                $terms = ts;
                $term = t;
            }, None => { $term_lifetime }
        }
    }}
}

macro_rules! parse_expression {
    ($tokens:expr, $arena:expr, $stack:expr) => {{
        let mut term = ProdEnd;
        let mut terms: Vec<ParseTerm>;
        let mut factors: ParseTerm;
        'expr: loop {
            terms = Vec::new();
            factors = Vec::new();
            loop {
                match term {
                    ProdEnd => parse_terms!($tokens, $arena, $stack, terms, factors, term, (|_| unreachable!()), s::Semi, break 'expr, continue 'expr),
                    OptEnd => parse_terms!($tokens, $arena, $stack, terms, factors, term, Opt, s::RBracket, break 'expr, continue 'expr),
                    RepEnd => parse_terms!($tokens, $arena, $stack, terms, factors, term, Rep, s::RBrace, break 'expr, continue 'expr),
                    GroupEnd => parse_terms!($tokens, $arena, $stack, terms, factors, term, Group, s::RParen, break 'expr, continue 'expr),
                }
            }
        }
        terms.push(factors);
        $arena.alloc(terms)[]
    }}
}

impl<'a> Parser<'a> {
    // Create a new parse context from a given string
    pub fn new() -> Parser<'a> {
        Parser { stack: Vec::new() }
    }

    fn lock<'b, 'c>(&'c mut self) -> ParserGuard<'a, 'b, 'c> {
        unsafe {
            ParserGuard {
                inner_: ::std::mem::transmute(self),
                marker_: ::std::kinds::marker::CovariantLifetime,
            }
        }
    }

    // Deserialize a Ebnf.
    pub fn parse<'b, 'c>(&'c mut self,
                     ctx: &'b ParserContext<'b>,
                     string: &'b [Ascii]) -> Result<::Ebnf<'b>, ::Error> {
        let ParserContext { ref arena } = *ctx;
        let mut ctx = self.lock();
        let ctx = ctx.deref_mut();
        let Parser { ref mut stack } = *ctx;
        let mut tokens = Tokens::new(string);
        let (title, next) = match tokens.next() {
            s::Lit(title) => { (Some(title), tokens.next()) },
            s::UnterminatedStringLiteral => return Err(::UnterminatedStringLiteral),
            next => (None, next)
        };
        if next != s::LBrace { return Err(::ExpectedLBrace) }

        let mut productions: FnvHashMap<&[Ascii], ParseExpr> = FnvHashMap::new();
        loop {
            match tokens.next() {
                s::Ident(id) => {
                    if tokens.next() != s::Equals { return Err(::ExpectedEquals) }
                    match productions.entry(id) {
                        hashmap::Vacant(entry) => { entry.set(parse_expression!(tokens, arena, stack)); }
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
