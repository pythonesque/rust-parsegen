use ascii::Ascii;
use std::marker;
use std::mem;
use std::raw::Slice;

pub use self::Token::*;

#[derive(PartialEq)]
pub enum Token<'a> {
    //Ident/*(&'a [Ascii])*/,
    Ident(&'a [Ascii]),
    //Lit/*(&'a [Ascii])*/,
    Lit(&'a [Ascii]),
    Equals,
    VBar,
    LParen, RParen,
    LBracket, RBracket,
    LBrace, RBrace,
    Semi,
    EOF,
    UnterminatedStringLiteral,
}

pub struct Tokens<'a> {
    ptr: *const Ascii,
    end: *const Ascii,
    //pub tok: &'a [Ascii],
    marker: marker::ContravariantLifetime<'a>,
}

macro_rules! consume_token {
    ($this:expr, $val:pat) => {{
        while $this.ptr != $this.end {
            let old = $this.ptr;
            $this.ptr = unsafe { $this.ptr.offset(1) };
            match unsafe { (*old).as_byte() } {
                $val => return true,
                b' ' | b'\x09' ... b'\x0d' => continue,
                _ => return false,
            }
        }
        false
    }}
}

impl<'a> Tokens<'a> {
    pub fn new(string: &'a [Ascii]) -> Tokens {
        unsafe {
            let p = string.as_ptr();
            Tokens {
                //tok: string,
                ptr: p,
                end: p.offset(string.len() as isize),
                marker: marker::ContravariantLifetime::<'a>,
            }
        }
    }

    #[inline(always)]
    //pub fn consume_equals(&mut self) -> bool { consume_token!(self, b'=') }


    // This is where the lexing happens.  Note that it does not handle string escaping.
    #[inline(always)]
    pub fn next(&mut self) -> Token<'a> {
        loop {
            unsafe {
                if self.ptr == self.end {
                    return EOF
                } else {
                    let old = self.ptr;
                    self.ptr = self.ptr.offset(1);
                    let new = match (*old).as_byte() {
                        b'=' => Equals,
                        b'|' => VBar,
                        b'(' => LParen,
                        b')' => RParen,
                        b'[' => LBracket,
                        b']' => RBracket,
                        b'{' => LBrace,
                        b'}' => RBrace,
                        b'.' | b';' => Semi,
                        // Double quoted literal start
                        b'"' => {
                            let start = self.ptr;
                            let mut old;
                            loop {
                                old = self.ptr;
                                if old == self.end { return UnterminatedStringLiteral }
                                self.ptr = self.ptr.offset(1);
                                if (*old).as_byte() == b'"' { break }
                            }
                            let len = old as usize - start as usize;
                            Lit(mem::transmute(Slice { data: start, len: len  }))
                            //self.tok = mem::transmute(Slice { data: start, len: len  });
                            //Lit
                        },
                        // Single quoted literal start
                        b'\'' => {
                            let start = self.ptr;
                            let mut old;
                            loop {
                                old = self.ptr;
                                if old == self.end { return UnterminatedStringLiteral }
                                self.ptr = self.ptr.offset(1);
                                if (*old).as_byte() == b'\'' { break }
                            }
                            let len = old as usize - start as usize;
                            Lit(mem::transmute(Slice { data: start, len: len }))
                            //self.tok = mem::transmute(Slice { data: start, len: len });
                            //Lit
                        },
                        // Skip whitespace.  This could probably be made more efficient.
                        b' ' | b'\x09' ... b'\x0d' => {
                            continue
                        },
                        // Identifier start
                        // NOTE: We rely on the fact that identifiers have nonzero length for
                        // correctness.  This is not presently an issue, but it is something to be
                        // aware of if you need to touch this code in the future.
                        _ => {
                            while self.ptr != self.end {
                                static TBL: [bool ; 256 as usize] = [
 false, false, false, false, false, false, false, false, false, true,  true,  true,  true,  true,  false, false,
 false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false,
 true,  false, true,  false, false, false, false, true,  true,  true,  false, false, false, false, true,  false,
 false, false, false, false, false, false, false, false, false, false, false, true,  false, true,  false, false,
 false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false,
 false, false, false, false, false, false, false, false, false, false, false, true,  false, true,  false, false,
 false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false,
 false, false, false, false, false, false, false, false, false, false, false, true,  true,  true,  false, false,
 false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false,
 false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false,
 false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false,
 false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false,
 false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false,
 false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false,
 false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false,
 false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false,
                            ];
                                if *TBL.get_unchecked((*self.ptr).as_byte() as usize) { break }
                                self.ptr = self.ptr.offset(1);
                            }
                            let len = self.ptr as usize - old as usize;
                            Ident(mem::transmute(Slice { data: old, len: len }))
                            //self.tok = mem::transmute(Slice { data: old, len: len });
                            //Ident
                        },
                    };
                    return new
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use ascii::AsciiCast;
    use test::Bencher;
    use super::Tokens;

    #[bench]
    fn bench_next(b: &mut Bencher) {
        static STRING: &'static [u8] = br#"(a b c d = f "ghi" j 'klm')"#;
        let string = STRING.to_ascii().unwrap();
        b.iter(|| {
            let mut tokens = Tokens::new(string);
            while tokens.next() != super::EOF {}
        })
    }
}
