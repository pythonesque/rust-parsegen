#![feature(unboxed_closures,unsafe_destructor,slicing_syntax,macro_rules)]

extern crate arena;
extern crate rustc;
extern crate test;

use rustc::util::nodemap::FnvHashMap;
use std::fmt;

pub use parser::{Parser, ParserContext};

mod scanner;
mod parser;

#[deriving(PartialEq)]
// The actual Exp structure.
// Note that it takes everything by reference, rather than owning it--this is mostly done just so
// we can allocate Ebnfs statically (since we don't have to call Vec).  It does complicate the code
// a bit by requiring us to have a ParseContext that holds an arena where lists are actually
// allocated.
/*enum SExp<'a> {
    F64(f64), // Float literal: 0.5
    List(&'a [SExp<'a>]), // List of SExps: ( a b c)
    Str(&'a str), // Plain old string literal: "abc"
}*/
pub struct Ebnf<'a> {
    title: Option<&'a [Ascii]>,
    productions: FnvHashMap<&'a [Ascii], Expr<'a>>,
    comment: Option<&'a [Ascii]>,
}

impl<'a> fmt::Show for Ebnf<'a> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        try!(write!(f, "Ebnf {{ title: {}, productions: {{\n", self.title.as_ref().map( |s| s.as_str_ascii() )));
        for (&id, &e) in self.productions.iter() {
            try!(write!(f, "<{}> {}: ", e.as_ptr(), id.as_str_ascii()));
            try!(show_expr(f, "", e, ".\n"));
        }
        write!(f, "}}, comment: {} }}", self.comment.as_ref().map( |s| s.as_str_ascii() ))
    }
}

pub type Expr<'a> = &'a [Term<'a>];

pub type Term<'a> = Vec<Factor<'a>>;

#[deriving(PartialEq)]
pub enum Factor<'a> {
    Ref(Expr<'a>),
    Lit(&'a [Ascii]),
    Opt(Expr<'a>),
    Rep(Expr<'a>),
    Group(Expr<'a>),
}

fn show_expr(f: &mut fmt::Formatter, l: &str, e: Expr, r: &str) -> fmt::Result {
    fn show_term(f: &mut fmt::Formatter, t: &Term) -> fmt::Result {
        let mut iter = t.iter();
        match iter.next() {
            Some(factor) => try!(write!(f, "{}", factor)),
            None => return Ok(())
        }
        for factor in iter {
            try!(write!(f, " {}", factor));
        }
        Ok(())
    }
    let mut iter = e.iter();
    try!(write!(f, "{}", l));
    match iter.next() {
        Some(term) => try!(show_term(f, term)),
        None => return Ok(())
    }
    for term in iter {
        try!(write!(f, " | "));
        try!(show_term(f, term))
    }
    write!(f, "{}", r)
}

impl<'a> fmt::Show for Factor<'a> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            Ref(e) => write!(f, "Ref {}", e.as_ptr()),
            Lit(s) => write!(f, "\"{}\"", s.as_str_ascii().escape_default()),
            Opt(e) => show_expr(f, "[ ", e, " ]"),
            Rep(e) => show_expr(f, "{ ", e, " }"),
            Group(e) => show_expr(f, "( ", e, " )"),
        }
    }
}

#[deriving(PartialEq,Show)]
pub enum Error {
    UnterminatedStringLiteral, // Missing an end double quote during string parsing
    ExpectedLBrace, // Expected a '{' token
    ExpectedEquals, // Expected an '=' token at the start of a production
    //UnexpectedEOF, // Usually means a missing ), but could also mean there were no tokens at all.
    ExpectedEOF, // More tokens after the list is finished, or after a literal if there is no list.
    DuplicateProduction, // Expected only one variant of the given production
    ExpectedProduction, // Expected an identifier or a '}' token (production start)
    MissingProduction, // EBNF referenced an invalid production
    ExpectedFactor, // Expected a factor, found something else
    ExpectedFactorOrEnd, // Expected a factor or end delimiter of some sort, found something else
}

/*fn parse(string: &[Ascii]) -> Result<(), Error> {
    let mut tokens = Tokens::new(string);
    loop {
        let tok = tokens.next();
        match try!(tok) {
            EOF => return Ok(()),
            Ident(s) => println!("Ident({})", s.as_str_ascii()),
            Literal(s) => println!("Literal({})", s.as_str_ascii()),
            t => println!("{}", t),
        }
    }
}*/

#[cfg(test)]
fn try_decode<'a, 'b, 'c>(parser: &'c mut Parser<'b>,
                          ctx: &'a ParserContext<'a>,
                          string: &'a [Ascii]) -> Result<Ebnf<'a>, Error> {
    parser.parse(ctx, string)
}

const EBNF_EBNF_STRING: &'static [u8] =
br#""EBNF defined in itself" {
syntax     = [ title ] "{" { production } "}" [ comment ].
production = identifier "=" expression ( "." | ";" ) .
expression = term { "|" term } .
term       = factor { factor } .
factor     = identifier
           | literal
           | "[" expression "]"
           | "(" expression ")"
           | "{" expression "}" .
identifier = character { character } .
title      = literal .
comment    = literal .
literal    = "'" character { character } "'"
           | '"' character { character } '"' .
character  = "a" .
}"#;

const ONE_LINE_EBNF_STRING: &'static [u8] =
br#""a" {
    a = "a1" ( "a2" | "a3" ) { "a4" } [ "a5" ] "a6" ;
    } "z""#;

const ASN1_EBNF_STRING: &'static [u8] = include_bin!("resources/asn1.ebnf");

#[bench]
fn bench_decode(b: &mut test::Bencher)
{
    //let string = EBNF_EBNF_STRING.to_ascii();
    let string = //ASN1_EBNF_STRING
                 ASN1_EBNF_STRING
                 //ONE_LINE_EBNF_STRING
                 .to_ascii();
    let ref mut parser = Parser::with_capacity(1024);
    let ref ctx = ParserContext::new();
    b.iter(|| {
        try_decode(parser, ctx, string).unwrap();
    })
}

#[test]
fn it_works() {
    //let mut ctx = ParserContext::new(); // Can put this either here...
    let string = //EBNF_EBNF_STRING
                ASN1_EBNF_STRING
                 //ONE_LINE_EBNF_STRING
                 .to_ascii();
    let mut parser = Parser::new();
    for _ in range(0, 1000u) {
        let ctx = ParserContext::new(); // or here...
        let foo = match try_decode(&mut parser, &ctx, string) {
            Ok(c) => {println!("{}", c); c }
            Err(e) => //{println!("{}", e); break },
                    fail!("{}", e),
        };
        /*for _ in range(0u16, 1000) {
            let ctx = ParserContext::new(); // or here...
            let _ = try_decode(&mut parser, &ctx, string);
        }*/
        break;
        //arena = ParserContext::new(); // or here...
        //println!("{}", foo);
        //break;
    }
}
