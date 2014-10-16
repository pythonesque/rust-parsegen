use std::kinds::marker;
use std::mem;
use std::raw::Slice;

#[deriving(PartialEq, Show)]
pub enum Token<'a> {
    Ident(&'a [Ascii]),
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
    marker: marker::ContravariantLifetime<'a>,
}

impl<'a> Tokens<'a> {
    pub fn new(string: &'a [Ascii]) -> Tokens {
        unsafe {
            let p = string.as_ptr();
            Tokens {
                ptr: p,
                end: p.offset(string.len() as int),
                marker: marker::ContravariantLifetime::<'a>,
            }
        }
    }

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
                    let new = match (*old).to_byte() {
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
                                if (*old).to_byte() == b'"' { break }
                            }
                            let len = old.to_uint() - start.to_uint();
                            Lit(mem::transmute(Slice { data: start, len: len  }))
                        },
                        // Single quoted literal start
                        b'\'' => {
                            let start = self.ptr;
                            let mut old;
                            loop {
                                old = self.ptr;
                                if old == self.end { return UnterminatedStringLiteral }
                                self.ptr = self.ptr.offset(1);
                                if (*old).to_byte() == b'\'' { break }
                            }
                            let len = old.to_uint() - start.to_uint();
                            Lit(mem::transmute(Slice { data: start, len: len }))
                        },
                        // Skip whitespace.  This could probably be made more efficient.
                        b' ' | b'\x09' ... b'\x0d' => {
                            continue
                        },
                        // Identifier start
                        _ => {
                            while self.ptr != self.end {
                                static TBL: [bool, .. 256 as uint] = [
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
                                if *TBL.unsafe_get((*self.ptr).to_byte() as uint) { break }
                                self.ptr = self.ptr.offset(1);
                            }
                            let len = self.ptr.to_uint() - old.to_uint();
                            Ident(mem::transmute(Slice { data: old, len: len }))
                        },
                    };
                    return mem::transmute(new)
                }
            }
        }
    }
}
