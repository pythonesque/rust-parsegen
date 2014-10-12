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
    pub fn next(&mut self) -> Token<'a> {
        loop {
            unsafe {
                if self.ptr == self.end {
                    return EOF
                } else {
                    let new = match (*self.ptr).to_byte() {
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
                            let mut len = 1;
                            loop {
                                let end = self.ptr.offset(len as int);
                                if end == self.end { return UnterminatedStringLiteral }
                                else if (*end).to_byte() == b'"' { break }
                                else { len += 1 }
                            }
                            let lit = Lit(mem::transmute(Slice { data: self.ptr.offset(1), len: len - 1}));
                            self.ptr = self.ptr.offset(len as int + 1);
                            return lit
                        },
                        // Single quoted literal start
                        b'\'' => {
                            let mut len = 1;
                            loop {
                                let end = self.ptr.offset(len as int);
                                if end == self.end { return UnterminatedStringLiteral }
                                else if (*end).to_byte() == b'\'' { break }
                                else { len += 1 }
                            }
                            let lit = Lit(mem::transmute(Slice { data: self.ptr.offset(1), len: len - 1}));
                            self.ptr = self.ptr.offset(len as int + 1);
                            return lit;
                        },
                        // Skip whitespace.  This could probably be made more efficient.
                        b' ' | b'\x09' ... b'\x0d' => {
                            self.ptr = self.ptr.offset(1);
                            continue
                        },
                        // Identifier start
                        _ => {
                            let mut len = 1;
                            loop {
                                let end = self.ptr.offset(len as int);
                                if end == self.end {
                                    let id = Ident(mem::transmute(Slice { data: self.ptr, len: len }));
                                    self.ptr = self.end;
                                    return id;
                                }
                                match (*end).to_byte() {
                                    b'=' | b'|' | b'(' | b')' | b'{' | b'}' | b'[' | b']' |
                                    b'.' | b';' | b'"' | b'\'' | b' ' | b'\x09' ... b'\x0d' => {
                                        break },
                                    _ => { len += 1 }
                                }
                            }
                            let id = Ident(mem::transmute(Slice { data: self.ptr, len: len }));
                            self.ptr = self.ptr.offset(len as int);
                            return id
                        },
                    };
                    self.ptr = self.ptr.offset(1);
                    return mem::transmute(new)
                }
            }
        }
    }
}
