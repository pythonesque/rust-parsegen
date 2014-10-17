#![feature(slicing_syntax)]

extern crate getopts;
extern crate parsegen;

use getopts::{optflag,getopts,OptGroup};
use parsegen::{Parser, ParserContext};
use std::io;
use std::io::fs::File;
use std::os;

fn parse<I, O>(parser: &mut Parser, mut input: I,  output: &mut O)
    where I: Reader, O: Writer {
    const CONTEXT_CAPACITY: uint = 8192;
    let string = input.read_to_end().unwrap().into_ascii();
    drop(input);
    let ref ctx = ParserContext::new(CONTEXT_CAPACITY);
    (writeln!(output, "{}", parser.parse(ctx, string[]))).unwrap();
}

fn print_usage(program: &str, _opts: &[OptGroup]) {
    let mut output = io::stdout();
    (writeln!(output, "Usage: {} [options]", program)).unwrap();
    (writeln!(output, "-h --help\tUsage")).unwrap();
}

fn main() {
    let args = os::args();

    let ref program = args[0];

    let ref mut output = io::stdout();

    let opts = [
        optflag("h", "help", "print this help menu")
    ];
    let matches = match getopts(args.tail(), opts) {
        Ok(m) => { m }
        Err(f) => { fail!(f.to_string()) }
    };
    const PARSER_CAPACITY: uint = 1024;
    let ref mut parser = Parser::with_capacity(PARSER_CAPACITY).unwrap();
    if matches.opt_present("h") {
        print_usage(program[], opts);
        return;
    }
    if matches.free.is_empty() {
        parse(parser, io::stdin(), output) 
    } else {
        for path in matches.free.iter().map ( |p| Path::new(p[]) ) {
            let file = File::open(&path).unwrap();
            parse(parser, file, output);
        }
    }
}
