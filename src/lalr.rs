use std::collections::{hash_map, trie_map, HashMap, HashSet, TrieMap, TrieSet, RingBuf, VecMap};

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


pub fn first<'a>(ebnf: &::Ebnf<'a>) -> TrieMap<HashSet<&'a [Ascii]>> {
    // http://david.tribble.com/text/lrk_parsing.html

    // 1. Add all of the nonterminals of the grammar to the nonterminals queue;
    let mut queue = ebnf.productions.iter().map( |&(_, e)| e ).collect::<RingBuf<_>>();
    let mut first = ebnf.productions.iter()
        .map( |&(_, e)| (e.as_ptr().to_uint().swap_bytes(), HashSet::new()) )
        .collect::<TrieMap<_>>();
    // TODO: Error here if there were duplicate production entries, or something.
    let epsilon = "".to_ascii(); // Hopefully zero runtime cost :)

    loop {
        // 2. Pop nonterminal X from the head of the queue
        let x = match queue.pop_front() { Some(x) => x, None => break };
        let xh = x.as_ptr().to_uint().swap_bytes(); // Index by const ptr, because we can :)
        let old_len = first[xh].len(); // Initial length of first set.

        // Compute a partial first(X) set for X
        for t in x.iter() { // For all rules with X as a LHS symbol
            // All hash indexing of first is guaranteed to succeed because we always insert a
            // new entry into the HashMap before we push into the queue.  So this shouldn't panic!
            let mut fs = t.iter();
            loop {
                match fs.next().map( |&f| f) {
                    None => { // X : epsilon
                        // 3. Add epsilon to first(X)
                        first[xh].insert(epsilon);
                        break
                    },
                    Some(::Lit(t)) => { // X : t B ... with terminal symbol t as the leftmost RHS symbol
                        // 4. Add symbol t to first(X)
                        first[xh].insert(t);
                        // Always break here, because we don't have a production so its first set
                        // cannot contain epsilon.
                        break;
                    },
                    Some(::Ref(p)) => { // X : P B ... with nonterminal symbol P
                        let ph = p.as_ptr().to_uint().swap_bytes();
                        if ph != xh {
                            // add to first(X) all terminal symbols other than epsilon
                            // that are currently in first(P).
                            // (first(P) may still be incomplete at this point.)
                            let mut p_first = first[ph].clone();
                            let contains_epsilon = p_first.remove(&epsilon);
                            first[xh].extend(p_first.into_iter());
                            // Repeat only if first(p) contains epsilon
                            if !contains_epsilon { break }
                        }
                    },
                    Some(::Opt(p)) | Some(::Rep(p)) => { // X : [P] B, P != X
                        let ph = p.as_ptr().to_uint().swap_bytes();
                        // add to first(X) all terminal symbols other than epsilon
                        // that are currently in first(P).
                        let mut p_first = match first.entry(ph) {
                            trie_map::Vacant(entry) => {
                                // We know first(p) always contains epsilon, since it is an
                                // opt/rep. Other than that, its terminals are identical to what
                                // is in the expr, so we punt on them for now.
                                let mut set = HashSet::new();
                                set.insert(epsilon);
                                entry.set(set);
                                queue.push_back(p);
                                continue
                            },
                            trie_map::Occupied(entry) => entry.get().clone()
                        };
                        p_first.remove(&epsilon);
                        first[xh].extend(p_first.into_iter());
                        // Because first(p) contains epsilon, we always continue here.
                    },
                    Some(::Group(p)) => { // X : (P) B, P != X
                        let ph = p.as_ptr().to_uint().swap_bytes();
                        // add to first(X) all terminal symbols other than epsilon
                        // that are currently in first(P).
                        let mut p_first = match first.entry(ph) {
                            trie_map::Vacant(entry) => {
                                entry.set(HashSet::new());
                                queue.push_back(p);
                                // We know first(p) cannot contain epsilon yet.
                                break;
                            },
                            trie_map::Occupied(entry) => entry.get().clone()
                        };
                        let contains_epsilon = p_first.remove(&epsilon);
                        first[xh].extend(p_first.into_iter());
                        // Repeat only if first(p) contains epsilon
                        if !contains_epsilon { break }
                    },
                }
            }
            if old_len != first[xh].len() || old_len == 0 {
                // If any terminals were added to first(X) in steps (3) through (6)
                // that were not already members of first(X),
                // or if first(X) is still empty, append X to the tail of the queue.
                queue.push_back(x);
                // Otherwise,
                // first(X) is complete
                // (and nonterminal X is no longer in the queue);
            }
        }
    }
    first
}

/*impl<T, R, Actions, Gotos, State, Terminal, NonTerminal> Table<T>
    where T: Map<State, Row<Actions, Gotos>>,
          Actions: Map<Terminal, Action<State, R>>,
          Gotos: Map<NonTerminal, State>,
          R: Rule<Terminal, NonTerminal>,
{

}*/
/*fn make_items(ebnf: &Ebnf<'a>) {

    let mut items = Vec::new();
    for &(_, e) in ebnf.productions.iter() { // rule lhs
        for t in e.iter() { // rule rhs
            for f in t.iter() { // rule factor
                items.push(f);
            }
        }
    }

    let mut item_sets = Vec::new();

    let rules = HashMap::new();
    let mut items = Vec::new();
    for &(_, e) in ebnf.productions.iter() {
        for t in e.iter() {
            for f in t.iter() {
                items.push(f);
            }
        }
    }
}*/

/*fn closure(ebnf: &Ebnf<'a>) {
    let ref i0 = ebnf[0];
    let closure_items = HashSet::new();
    //let mut queue = ebnf.productions.iter().map( |&(_, e)| e ).collect::<RingBuf<_>>();
    let mut stack = Vec::new();
    stack.push(i0);
    loop {
        match stack.pop() {
            Some(e) => {
                if closure_items.insert(e) {
                }
            },
            None => break
        }
    }
}*/

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
    use parser::{Parser, ParserContext};
    use std::hash::sip::{SipHasher, SipState};
    use test::Bencher;

    const EBNF_EBNF_STRING: &'static [u8] = include_bin!("resources/ebnf.ebnf");

    const ONE_LINE_EBNF_STRING: &'static [u8] = include_bin!("resources/one_line.ebnf");

    const ASN1_EBNF_STRING: &'static [u8] = include_bin!("resources/asn1.ebnf");

    const PAREN_EXPR: &'static [u8] = include_bin!("resources/paren_expr.ebnf");

    #[test]
    pub fn test_first_set() {
        let mut parser = Parser::<SipHasher, SipState>::with_capacity(8).unwrap();
        let ctx = ParserContext::new(8);
        let string = //EBNF_EBNF_STRING
                     ASN1_EBNF_STRING
                     //ONE_LINE_EBNF_STRING
                     //PAREN_EXPR
                     .to_ascii();
        let ebnf = parser.parse(&ctx, string).unwrap();
        println!("{}", ebnf);
        let first = lalr::first(&ebnf);
        println!("{}", first);
    }

    #[bench]
    pub fn bench_first_setb(b: &mut Bencher) {
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
                let first = lalr::first(&ebnf);
            //}
        });
    }
}
