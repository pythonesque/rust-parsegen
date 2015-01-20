use Factor as F;

use std::collections::RingBuf;

use util::fast_bit_set::{BitSet, BitSetStorage};

/*struct Table<T> {
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

trait Rule<E, N> {}*/

const EPSILON: usize = 0;

pub fn first<'a>(ebnf: &::Ebnf<'a>) -> Option<BitSetStorage<u32>> {
    // http://david.tribble.com/text/lrk_parsing.html

    // 1. Add all of the nonterminals of the grammar to the nonterminals queue;
    let mut queue = (0 .. ebnf.productions.len()).collect::<RingBuf<_>>();
    let first = match BitSetStorage::new(ebnf.productions.len(), ebnf.terminals.len(), 0) {
        Some(first) => first,
        None => return None
    };
    // TODO: Error here if there were duplicate production entries, or something.

    loop {
        // 2. Pop nonterminal X from the head of the queue
        let xh = match queue.pop_front() { Some(xh) => xh, None => break };
        let x_first = first.index(xh);
        let x_contains_epsilon = x_first.contains(EPSILON);
        let old_len = x_first.len(); // Initial length of first set.

        let x = ebnf.productions[xh].1;
        // Compute a partial first(X) set for X
        for t in x.iter() { // For all rules with X as a LHS symbol
            let mut fs = t.iter();
            loop {
                match fs.next().map( |&f| f) {
                    None => { // X : epsilon
                        // 3. Add epsilon to first(X)
                        x_first.insert(EPSILON);
                        break
                    },
                    Some(F::Lit(EPSILON, _)) => continue, // Epsilon terminals are ignored
                    Some(F::Lit(t, _)) => { // X : t B ... with terminal symbol t as the leftmost RHS symbol
                        // 4. Add symbol t to first(X)
                        x_first.insert(t);
                        // Always break here, because we don't have a production so its first set
                        // cannot contain epsilon.
                        break;
                    },
                    Some(F::Ref(ph)) => { // X : P B ... with nonterminal symbol P
                        if ph != xh {
                            // add to first(X) all terminal symbols other than epsilon
                            // that are currently in first(P).
                            // (first(P) may still be incomplete at this point.)
                            let p_first = first.index(ph);
                            let contains_epsilon = p_first.contains(EPSILON);
                            x_first.union_with(&p_first);
                            // Repeat only if first(p) contains epsilon
                            if !contains_epsilon { break }
                            if !x_contains_epsilon { x_first.remove(EPSILON); }
                        }
                    },
                    Some(F::Opt(ph)) | Some(F::Rep(ph)) => { // X : [P] B, P != X
                        // add to first(X) all terminal symbols other than epsilon
                        // that are currently in first(P).
                        let p_first = first.index(ph);
                        p_first.insert(EPSILON);
                        x_first.union_with(&p_first);
                        if !x_contains_epsilon { x_first.remove(EPSILON); }
                        // Because first(p) contains epsilon, we always continue here.
                    },
                    Some(F::Group(ph)) => { // X : (P) B, P != X
                        // add to first(X) all terminal symbols other than epsilon
                        // that are currently in first(P).
                        let p_first = first.index(ph);
                        let contains_epsilon = p_first.contains(EPSILON);
                        x_first.union_with(&p_first);
                        // Repeat only if first(p) contains epsilon
                        if !contains_epsilon { break }
                        if !x_contains_epsilon { x_first.remove(EPSILON); }
                    },
                }
            }
            if old_len != x_first.len() || old_len == 0 {
                // If any terminals were added to first(X) in steps (3) through (6)
                // that were not already members of first(X),
                // or if first(X) is still empty, append X to the tail of the queue.
                queue.push_back(xh);
                // Otherwise,
                // first(X) is complete
                // (and nonterminal X is no longer in the queue);
            }
        }
    }
    Some(first)
}

pub fn first_for<'a>(set: &BitSet<u32>, term: ::Term<'a>, lookahead: usize, _ebnf: &::Ebnf<'a>, first: &BitSetStorage<u32>) {
    for &f in term.iter() {
        match f {
            F::Lit(EPSILON, _) => continue,
            F::Lit(t, _) => {
                set.insert(t);
                return
            },
            F::Ref(s) | F::Group(s) => {
                set.union_with(&first.index(s));
                if !set.remove(EPSILON) { return }
            },
            F::Opt(s) | F::Rep(s) => {
                set.union_with(&first.index(s));
                set.remove(EPSILON);
            }
        }
    }
    set.insert(lookahead);
}

/*mod rule_table {
    type Mark = u8;

    pub struct RuleTable {
        mark1: Mark,
        mark2: Mark,
        row_size: usize,
        free_list: FreeList<'a, RuleSet, RuleSet>
        table: Vec<Hole<'a, >>,
        terms: Vec<usize>,
        table: Vec<Mark>, // rule_count * (symbols + 2)
        dirty: BitvSet, // per-rule dirty flag set when table is cleared
    }

    impl RuleTable {
        pub fn new(ebnf: ::Ebnf<'a>) -> Option<RuleTable> {
            let row_size = ebnf.terminals.count() + ebnf.productions.count();
            let size = match ebnf.n_terms.checked_mul(row_size) { Some(s) => s, None => return None };
            Some(RuleTable {
                mark1: 1,
                mark2: 2,
                row_size: row_size,
                table: {
                    let mut table = Vec::with_capacity(size);
                    // This is safe because we will clear each row if the dirty bit is not set before
                    // providing access.
                    unsafe { table.set_len(size); }
                    table
                },
                dirty: BitvSet::with_capacity(ebnf.n_terms),
            })
        }

        pub fn row(row: usize, col: uint) {
            if dirty.insert(row) {
                table[row]
            }
        }
    }

    pub enum Symbol {
        Term(usize),
        Nonterm(usize),

    }

    /*struct Symbols {

    }*/
}*/

/*pub fn gen_closure_items<'a>(ebnf: ebnf: ::Ebnf<'a>, first: &[BitvSet]) {

}*/

/*pub fn closure<'a>(kernel: Item<'a>, ebnf: &::Ebnf<'a>, first: &[HashSet<&'a Ascii>]) {
    let mut set = HashSet::new();
    let mut queue = RingBuf::new();
    queue.push_back(kernel);
    loop {
        let item = match queue.pop_ront() { Some(i) => i, None => break };
        if set.insert(item) {
            let mut new_term = item.term.split_at(1);
            match item[0] {
                Lit(_) => continue,
                Ref(i) | Group(i) => {
                    for &lookahead in first[i].iter() {
                        queue.push_back(Item { lhs: i, term: ebnf.productions[i].1
                    }
                }
            }
            for &lookahead in first[item.lhs].iter() {
                queue.push_back(Item { lhs: item.term});
            }
        }
    }
}*/

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


/*enum Lookahead<'a> {
    End,
    Symbol(&'a Ascii),
}*/

/*struct Item<'a> {
    lhs: usize,
    term: ::ParseTerm<'a>,
    lookahead: Lookahead<'a>,
}*/


//+THIS method is the bottleneck for the entire program!

//+THIS algorithm can be replaced with a better algorithm which
//+ executes in O(2s) time and O((n+t)r) space, where s = this.m_size,
//+ r = Grammar.m_nRules, n = Grammar.m_nNonterms, t = Grammar.m_nTerms;
//+
//+Algorithm:
//+ // initialize
//+ init ruleTable,
//+   each ruleTable[rI][s] represents closure item [rI. B -> . X Y, s];
//+   for each ruleTable[rI],
//+     ruleTable[rI] = null;
//+ mark1 += 2, mark2 += 2;
//+ if mark2 > BYTE_MAX,
//+   reset the ruleTable, and mark1 = 0, mark2 = 1;
//+ // generate closures for kernel items
//+ for each kernel item in this set, [rN. A -> B . S T, u],
//+   if ruleTable[rN] is null,
//+     ruleTable[rN] = allocate symbol table, byte array[n+t];
//+   // generate closure items from the kernel item
//+   for each rule rG with S as LHS (rule group for S), [rG. S -> X Y],
//+     for each symbol A in first(S T u),
//+       set ruleTable[rG][A] = mark1;
//+   end for;
//+ end for;
//+ // generate closures for non-kernel closure items
//+ do
//+   for each rule rI where ruleTable[rI] not null,
//+     for each symbol S in ruleTable[rI],
//+       if ruleTable[rI][S] == mark1,
//+         // generate closure items from [rI. B -> . X Y, S],
//+         for each rule rG with X as LHS (rule group for X),
//+           if ruleTable[rG][X] != mark2,
//+             set ruleTable[rG][X] = mark1;
//+         set ruleTable[rI][S] = mark2;
//+         didWork = true;
//+       end if;
//+     end for;
//+   end for;
//+ while didWork;
//+ // convert ruleTable entries into closure items
//+ for each rule rI where ruleTable[rI] not null,
//+   for each symbol S in ruleTable[rI],
//+     if ruleTable[rI][S] == mark1|mark2,
//+       create closure item, [rI. B -> . X Y, S];
//+       add item to this set;
//+     end if;
//+   end for;
//+ end for;
//+ // clean up
//+ for each ruleTable[rI],
//+   deallocate (recache) ruleTable[rI];
//+ end.
//pub fn generate_

/*impl<R> Table<VecMap<Row<VecMap<Action<usize, R>>, VecMap<uint>>>>
    where R: Rule<usize, uint>,
{
    type T = VecMap<Row<VecMap<Action<usize, R>>, VecMap<uint>>>;
    type Actions = VecMap<Action<usize, R>>;
    type Gotos = VecMap<usize>;
}*/

#[cfg(test)]
mod tests {
    use lalr;
    use ascii::AsciiCast;
    use util::fast_bit_set::BitSetStorage;
    use parser::{Parser, ParserContext};
    use std::hash::SipHasher;
    use test::Bencher;

    const EBNF_EBNF_STRING: &'static [u8] = include_bytes!("resources/ebnf.ebnf");

    const ONE_LINE_EBNF_STRING: &'static [u8] = include_bytes!("resources/one_line.ebnf");

    const ASN1_EBNF_STRING: &'static [u8] = include_bytes!("resources/asn1.ebnf");

    const PAREN_EXPR: &'static [u8] = include_bytes!("resources/paren_expr.ebnf");

    #[test]
    pub fn first_set_t() {
        let mut parser = Parser::<SipHasher>::with_capacity(8).unwrap();
        let ctx = ParserContext::new(1024);
        let string = //EBNF_EBNF_STRING
                     ASN1_EBNF_STRING
                     //ONE_LINE_EBNF_STRING
                     //PAREN_EXPR
                     .to_ascii()
                     .unwrap();
        let ebnf = parser.parse(&ctx, string).unwrap();
        println!("{:?}", ebnf);
        let first = lalr::first(&ebnf).unwrap();
        println!("{:?}", first);
    }

    #[test]
    pub fn first_for() {
        let mut parser = Parser::<SipHasher>::with_capacity(8).unwrap();
        let ctx = ParserContext::new(16);
        let string = //EBNF_EBNF_STRING
                     //ASN1_EBNF_STRING
                     //ONE_LINE_EBNF_STRING
                     PAREN_EXPR
                     .to_ascii()
                     .unwrap();
        let ebnf = parser.parse(&ctx, string).unwrap();
        println!("{:?}", ebnf);
        let firsts = lalr::first(&ebnf).unwrap();
        println!("{:?}", firsts);
        let end = ebnf.terminals.len();
        let sets = BitSetStorage::new(1, ebnf.terminals.len(), 0).unwrap();
        let set = sets.index(0);
        let first = lalr::first_for(&set, &ebnf.productions[0].1[1][1 .. ], end, &ebnf, &firsts);
        // {1, 3, 4}
        println!("{:?}", first);
    }

    #[bench]
    pub fn first_set_b(b: &mut Bencher) {
        let mut parser = Parser::<SipHasher>::with_capacity(1024).unwrap();
        //let ctx = ParserContext::new(8);
        let string = //EBNF_EBNF_STRING
                     ASN1_EBNF_STRING
                     //ONE_LINE_EBNF_STRING
                     .to_ascii()
                     .unwrap();
        b.iter(|| {
            let ref ctx = ParserContext::new(0x100);
            //let ref ctx = ParserContext::new(80);
            //let ref ctx = ParserContext::new(8);
            //let ref ctx = ParserContext::new(32);
            //for _ in range(0, 10i8) {
                let ebnf = parser.parse(ctx, string).unwrap();
                let first = lalr::first(&ebnf).unwrap();
            //}
        });
    }
}
