#![feature(associated_types,unboxed_closures,unsafe_destructor,slicing_syntax,macro_rules,default_type_params,tuple_indexing)]

extern crate arena;
extern crate libc;
//extern crate rustc;
//extern crate sync;
extern crate test;

//use rustc::util::nodemap::FnvHashMap;
use std::fmt;
use std::raw::Repr;

pub use parser::{Parser, ParserContext};

mod lalr;
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
    //productions: FnvHashMap<&'a [Ascii], Expr<'a>>,
    //productions: HashMap<&'a [Ascii], Expr<'a>, XXHasher>,

    //productions: Vec<(&'a [Ascii], Expr<'a>)>,//HashMap<&'a [Ascii], Expr<'a>, FnvHasherDefault>,
    productions: Vec<(&'a [Ascii], Expr<'a>)>,//HashMap<&'a [Ascii], Expr<'a>, FnvHasherDefault>,
    comment: Option<&'a [Ascii]>,
}

impl<'a> fmt::Show for Ebnf<'a> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        try!(write!(f, "Ebnf {{ title: {}, productions: {{\n", self.title.as_ref().map( |s| s.as_str_ascii() )));
        //for (&id, &e) in self.productions.iter() {
        for &(id, e) in self.productions.iter() {
            try!(write!(f, "<{}> {}: ", e.as_ptr(), id.as_str_ascii()));
            try!(show_expr(f, "", e, ".\n"));
        }
        write!(f, "}}, comment: {} }}", self.comment.as_ref().map( |s| s.as_str_ascii() ))
    }
}

pub type Expr<'a> = &'a [Term<'a>];

pub type Term<'a> = &'a [Factor<'a>];

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
            Ref(e) => write!(f, "Ref {}({})", e.repr().data, e.repr().len),
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

#[cfg(test)]
mod tests {
    use test::Bencher;
    use parser::{Parser, ParserContext};

    fn try_decode<'a, 'b, 'c>(parser: &'c mut Parser<'b>,
                              ctx: &'a ParserContext<'a>,
                              string: &'a [Ascii]) -> Result<::Ebnf<'a>, ::Error> {
        parser.parse(ctx, string)
    }

    const EBNF_EBNF_STRING: &'static [u8] = include_bin!("resources/ebnf.ebnf");

    const ONE_LINE_EBNF_STRING: &'static [u8] = include_bin!("resources/one_line.ebnf");

    const ASN1_EBNF_STRING: &'static [u8] = include_bin!("resources/asn1.ebnf");

    const PAREN_EXPR: &'static [u8] = include_bin!("resources/paren_expr.ebnf");

    #[bench]
    fn bench_decode(b: &mut Bencher)
    {
        //let string = EBNF_EBNF_STRING.to_ascii();
        let string = //EBNF_EBNF_STRING
                     ASN1_EBNF_STRING
                     //PAREN_EXPR
                     //ONE_LINE_EBNF_STRING
                     .to_ascii();
        /*let ref mut parser = Parser::with_capacity(1024);
        let ref ctx = ParserContext::new(8192);*/
        /*static mut static_parser: *mut Parser<'static> = 0 as *mut _;//unsafe { std::mem::uninitialized(); }

        static START: Once = ONCE_INIT;

        START.doit(|| {
            unsafe {
                static_parser = ::std::mem::transmute(box Parser::with_capacity(1024).unwrap());
            }
        });

        let parser = unsafe { &mut *static_parser };*/

        let ref mut parser = Parser::with_capacity(1024).unwrap();
        //let ref mut parser = Parser::new().unwrap();
        //let ref ctx = ParserContext::new(0x1000);
        b.iter(|| {
            let ref ctx = ParserContext::new(0x100);
            //let ref ctx = ParserContext::new(80);
            //let ref ctx = ParserContext::new(8);
            //let ref ctx = ParserContext::new(32);
            //for _ in range(0, 10i8) {
                try_decode(parser, ctx, string).unwrap();
            //}
        });
    }

    #[test]
    fn it_works() {
        //let mut ctx = ParserContext::new(); // Can put this either here...
        let string = //EBNF_EBNF_STRING
                    ASN1_EBNF_STRING
                     //ONE_LINE_EBNF_STRING
                     .to_ascii();
        //let mut parser = Parser::new().unwrap();
        let mut parser = Parser::with_capacity(1024).unwrap();
        for _ in range(0, 1000u) {
            //let ctx = ParserContext::new(8); // or here...
            let ctx = ParserContext::new(8192);
            let /*foo*/_ = match try_decode(&mut parser, &ctx, string) {
                Ok(c) => {println!("{}", c); c }
                Err(e) => //{println!("{}", e); break },
                        panic!("{}", e),
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
}
