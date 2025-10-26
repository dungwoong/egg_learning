use crate::*;
use std::result;

type Result = result::Result<(), ()>;

#[derive(Default)]
struct Machine {
    reg: Vec<Id>,
    // a buffer to re-use for lookups
    lookup: Vec<Id>,
}

#[derive(Debug, Default, Copy, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
struct Reg(u32);

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Program<L> {
    instructions: Vec<Instruction<L>>,
    subst: Subst,
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum Instruction<L> {
    Bind { node: L, i: Reg, out: Reg },
    Compare { i: Reg, j: Reg },
    Lookup { term: Vec<ENodeOrReg<L>>, i: Reg },
    Scan { out: Reg },
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum ENodeOrReg<L> {
    ENode(L),
    Reg(Reg),
}

impl Machine {
    #[inline(always)]
    fn reg(&self, reg: Reg) -> Id {
        self.reg[reg.0 as usize]
    }

    fn run<L, N>(
        &mut self,
        egraph: &EGraph<L, N>,
        instructions: &[Instruction<L>],
        subst: &Subst,
        yield_fn: &mut impl FnMut(&Self, &Subst) -> Result,
    ) -> Result
    where
        L: Language,
        N: Analysis<L>,
    {
        let mut instructions = instructions.iter();
        while let Some(instruction) = instructions.next() {
            match instruction {
                Instruction::Bind { i, out, node } => {
                    let remaining_instructions = instructions.as_slice(); // NOTE get rest of instructions
                    let eclass = &egraph[self.reg(*i)]; // lookup e-class corresponding to whatever's in register i
                    return eclass.for_each_matching_node(node, |matched| { // e.g. * (?x, ?y), make sure it's * and 2 children
                        // like DFS, go back to the branching point
                        self.reg.truncate(out.0 as usize); // so you want to go back in the tree or something, so you get rid of everything after?
                        matched.for_each(|id| self.reg.push(id)); // push child ids e.g. +(3, 5) you push 3 and 5 I think
                        self.run(egraph, remaining_instructions, subst, yield_fn) // run remaining instructions (for each match btw)
                    });
                }
                Instruction::Scan { out } => {
                    let remaining_instructions = instructions.as_slice();
                    for class in egraph.classes() {
                        self.reg.truncate(out.0 as usize);
                        self.reg.push(class.id);
                        self.run(egraph, remaining_instructions, subst, yield_fn)? // ? means return val or error if needed
                    }
                    return Ok(());
                }
                // continue if i and j are in the same e-class
                Instruction::Compare { i, j } => {
                    if egraph.find(self.reg(*i)) != egraph.find(self.reg(*j)) {
                        return Ok(()); // ok just means to stop the search
                    }
                }
                Instruction::Lookup { term, i } => {
                    // NOTE so lookup only works when you already have the children I guess, so you start w children and then u get the parent...?
                    self.lookup.clear();
                    for node in term {
                        match node {
                            // node is an operator or literal
                            ENodeOrReg::ENode(node) => {
                                // lookup is a vec of Id
                                let look = |i| self.lookup[usize::from(i)]; // closure(anonymous function that can capture values from its own scope)
                                match egraph.lookup(node.clone().map_children(look)) { // all children should be in lookup already(topological order)
                                    // the e-graph looks up the node and if it finds a matching node it'll return the id
                                    // NOTE the egraph lookup might just be looking at the hashcons, cuz look essentially canonicalizes the ids I think
                                    Some(id) => self.lookup.push(id),
                                    None => return Ok(()),
                                }
                            }
                            ENodeOrReg::Reg(r) => {
                                // register, get canonical e-class id of whatever's in the register and push it
                                self.lookup.push(egraph.find(self.reg(*r)));
                            }
                        }
                    }

                    // i is the target register for the root of the term
                    // so if the last item in lookup doesn't match the target register's e-class, we prune this branch
                    let id = egraph.find(self.reg(*i));
                    if self.lookup.last().copied() != Some(id) {
                        return Ok(());
                    }
                }
            }
        }

        yield_fn(self, subst)
    }
}

struct Compiler<L> {
    v2r: IndexMap<Var, Reg>,
    free_vars: Vec<HashSet<Var>>,
    subtree_size: Vec<usize>,
    todo_nodes: HashMap<(Id, Reg), L>,
    instructions: Vec<Instruction<L>>,
    next_reg: Reg,
}

impl<L: Language> Compiler<L> {
    fn new() -> Self {
        Self {
            free_vars: Default::default(),
            subtree_size: Default::default(),
            v2r: Default::default(),
            todo_nodes: Default::default(),
            instructions: Default::default(),
            next_reg: Reg(0),
        }
    }

    fn add_todo(&mut self, pattern: &PatternAst<L>, id: Id, reg: Reg) {
        match &pattern[id] {
            ENodeOrVar::Var(v) => {
                if let Some(&j) = self.v2r.get(v) {
                    self.instructions.push(Instruction::Compare { i: reg, j })
                } else {
                    self.v2r.insert(*v, reg);
                }
            }
            ENodeOrVar::ENode(pat) => {
                self.todo_nodes.insert((id, reg), pat.clone());
            }
        }
    }

    fn load_pattern(&mut self, pattern: &PatternAst<L>) {
        let len = pattern.len();
        self.free_vars = Vec::with_capacity(len);
        self.subtree_size = Vec::with_capacity(len);

        for node in pattern {
            let mut free = HashSet::default();
            let mut size = 0;
            match node {
                ENodeOrVar::ENode(n) => {
                    size = 1;
                    for &child in n.children() {
                        // NOTE get free vars and subtree size(since we iterate in topological order)
                        free.extend(&self.free_vars[usize::from(child)]);
                        size += self.subtree_size[usize::from(child)];
                    }
                }
                ENodeOrVar::Var(v) => {
                    free.insert(*v); // base case, no children, just insert v
                }
            }
            self.free_vars.push(free); // so free vars and subtree size stores these items FOR EACH NODe in the pattern
            self.subtree_size.push(size);
        }
    }

    fn next(&mut self) -> Option<((Id, Reg), L)> {
        // we take the max todo according to this key
        // - prefer grounded
        // - prefer more free variables
        // - prefer smaller term
        let key = |(id, _): &&(Id, Reg)| {
            let i = usize::from(*id);
            let n_bound = self.free_vars[i]
                .iter()
                .filter(|v| self.v2r.contains_key(*v))
                .count();
            let n_free = self.free_vars[i].len() - n_bound;
            let size = self.subtree_size[i] as isize;
            (n_free == 0, n_free, -size)
        };

        self.todo_nodes
            .keys()
            .max_by_key(key)
            .copied()
            .map(|k| (k, self.todo_nodes.remove(&k).unwrap()))
    }

    /// check to see if this e-node corresponds to a term that is grounded by
    /// the variables bound at this point
    fn is_ground_now(&self, id: Id) -> bool {
        self.free_vars[usize::from(id)]
            .iter()
            .all(|v| self.v2r.contains_key(v))
    }

    fn compile(&mut self, patternbinder: Option<Var>, pattern: &PatternAst<L>) {
        self.load_pattern(pattern); // NOTE populate free vars and subtree size FOR EACH node in the pattern
        let root = pattern.root();

        let mut next_out = self.next_reg; // I dunno bro

        // Check if patternbinder already bound in v2r
        // Behavior common to creating a new pattern
        let add_new_pattern = |comp: &mut Compiler<L>| {
            if !comp.instructions.is_empty() {
                // After first pattern needs scan
                // NOTE so the first TODO will probably add an instruction to find the root. THEN, we must scan after everytime I guess
                comp.instructions
                    .push(Instruction::Scan { out: comp.next_reg });
            }
            comp.add_todo(pattern, root, comp.next_reg);
        };

        // NOTE: this is for multipattern
        if let Some(v) = patternbinder {
            // TODO we can see that add_new_pattern does almost the same thing as the if statement
            // so if it's not bound yet, we have to do a scan. It just tries to run the remaining instruction set on every e-class
            // if it IS bound, then we just add a todo of the pattern from node i, ok that makes sense I guess...
            // I don't get how they deal with shared variables between multiple patterns, but I guess it's not a big issue if I'm porting egg.
            // the Compare is in add_todo, so maybe that has something to do with it
            if let Some(&i) = self.v2r.get(&v) {
                // patternbinder already bound
                self.add_todo(pattern, root, i);
            } else {
                // patternbinder is new variable
                next_out.0 += 1;
                add_new_pattern(self);
                self.v2r.insert(v, self.next_reg); //add to known variables.
            }
        } else {
            // No pattern binder
            next_out.0 += 1;
            add_new_pattern(self);
        }

        // NOTE next() takes from todo_nodes btw
        while let Some(((id, reg), node)) = self.next() {
            // NOTE is_ground_now checks if all the node's children are in registers already
            // skip leaf nodes cuz we don't need to lookup for those(why?)
            if self.is_ground_now(id) && !node.is_leaf() {
                let extracted = pattern.extract(id); // get subtree rooted at this node(?)
                // lookup e.g. if we have +(?x 1) and we already have x in registers, we can do a lookup for the +??
                // I think it's faster than other stuff, so we just do this when we CAN
                self.instructions.push(Instruction::Lookup {
                    i: reg,
                    term: extracted
                        .iter()
                        .map(|n| match n {
                            ENodeOrVar::ENode(n) => ENodeOrReg::ENode(n.clone()),
                            ENodeOrVar::Var(v) => ENodeOrReg::Reg(self.v2r[v]),
                        })
                        .collect(),
                });
            } else {
                // so if you can't try a lookup, you try a DFS kinda thing where you start to bind stuff. e.g. if + is your next thing, bind to a + if possible, and then look for its children
                // NOTE so this is where we do binding and comparing and then more binding. It's honestly kinda like a BFS or a priority queue search kinda since next() prioritizes
                let out = next_out;
                next_out.0 += node.len() as u32;

                // zero out the children so Bind can use it to sort
                let op = node.clone().map_children(|_| Id::from(0));
                self.instructions.push(Instruction::Bind {
                    i: reg,
                    node: op,
                    out,
                });

                for (i, &child) in node.children().iter().enumerate() {
                    self.add_todo(pattern, child, Reg(out.0 + i as u32));
                }
            }
        }
        self.next_reg = next_out;
    }

    fn extract(self) -> Program<L> {
        let mut subst = Subst::default();
        for (v, r) in self.v2r {
            subst.insert(v, Id::from(r.0 as usize));
        }
        Program {
            instructions: self.instructions,
            subst,
        }
    }
}

impl<L: Language> Program<L> {
    pub(crate) fn compile_from_pat(pattern: &PatternAst<L>) -> Self {
        let mut compiler = Compiler::new();
        compiler.compile(None, pattern);
        let program = compiler.extract();
        log::debug!("Compiled {:?} to {:?}", pattern.as_ref(), program);
        program
    }

    pub(crate) fn compile_from_multi_pat(patterns: &[(Var, PatternAst<L>)]) -> Self {
        // NOTE seems like the vars are new vars that are made, and they bind the root of the pattern to the var(chatGPT)
        let mut compiler = Compiler::new();
        for (var, pattern) in patterns {
            compiler.compile(Some(*var), pattern);
        }
        compiler.extract()
    }

    pub fn run_with_limit<A>(
        &self,
        egraph: &EGraph<L, A>,
        eclass: Id,
        mut limit: usize,
    ) -> Vec<Subst>
    where
        A: Analysis<L>,
    {
        assert!(egraph.clean, "Tried to search a dirty e-graph!");

        if limit == 0 {
            return vec![];
        }

        let mut machine = Machine::default();
        assert_eq!(machine.reg.len(), 0);
        machine.reg.push(eclass);

        let mut matches = Vec::new();
        machine
            .run(
                egraph,
                &self.instructions,
                &self.subst,
                &mut |machine, subst| {
                    if !egraph.analysis.allow_ematching_cycles() {
                        if let Some((first, rest)) = machine.reg.split_first() {
                            if rest.contains(first) {
                                return Ok(());
                            }
                        }
                    }

                    let subst_vec = subst
                        .vec
                        .iter()
                        // HACK we are reusing Ids here, this is bad
                        .map(|(v, reg_id)| (*v, machine.reg(Reg(usize::from(*reg_id) as u32))))
                        .collect();
                    matches.push(Subst { vec: subst_vec });
                    limit -= 1;
                    if limit != 0 {
                        Ok(())
                    } else {
                        Err(())
                    }
                },
            )
            .unwrap_or_default();

        log::trace!("Ran program, found {:?}", matches);
        matches
    }
}
