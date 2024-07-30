mod unroll;

use abc::Abc;
use aig::{Aig, AigEdge};
use logic_form::{Clause, Cube, Lit, LitMap, Var, VarMap};
use minisat::SimpSolver;
use satif::Satif;
use std::{
    collections::{HashMap, HashSet},
    ffi::{c_char, c_int, c_uint, c_void, CStr},
    mem::{forget, take, transmute},
    slice::from_raw_parts,
    usize,
};
pub use unroll::*;

#[derive(Clone, Default, Debug)]
pub struct Transys {
    pub inputs: Vec<Var>,
    pub latchs: Vec<Var>,
    pub init: Cube,
    pub bad: Lit,
    pub init_map: VarMap<Option<bool>>,
    pub constraints: Cube,
    pub trans: Vec<Clause>,
    pub num_var: usize,
    is_latch: VarMap<bool>,
    next_map: LitMap<Lit>,
    prev_map: LitMap<Lit>,
    pub dependence: VarMap<Vec<Var>>,
    pub max_latch: Var,
    pub latch_group: VarMap<u32>,
    pub groups: HashMap<u32, Vec<Var>>,
}

impl Transys {
    fn compress_deps_rec(
        v: Var,
        deps: &mut VarMap<Vec<Var>>,
        domain: &HashSet<Var>,
        compressed: &mut HashSet<Var>,
    ) {
        if compressed.contains(&v) {
            return;
        }
        for d in 0..deps[v].len() {
            Self::compress_deps_rec(deps[v][d], deps, domain, compressed);
        }
        let mut dep = HashSet::new();
        for d in deps[v].iter() {
            if domain.contains(d) {
                dep.insert(*d);
                continue;
            }
            for dd in deps[*d].iter() {
                dep.insert(*dd);
            }
        }
        deps[v] = dep.into_iter().collect();
        deps[v].sort();
        compressed.insert(v);
    }

    fn compress_deps(mut deps: VarMap<Vec<Var>>, domain: &HashSet<Var>) -> VarMap<Vec<Var>> {
        let mut compressed: HashSet<Var> = HashSet::new();
        for v in 0..deps.len() {
            let v = Var::new(v);
            Self::compress_deps_rec(v, &mut deps, &domain, &mut compressed)
        }
        for v in 0..deps.len() {
            let v = Var::new(v);
            if !domain.contains(&v) {
                deps[v].clear();
            }
        }
        deps
    }

    pub fn abc_preprocess(mut aig: Aig) -> Aig {
        let num_input = aig.inputs.len();
        let num_latchs = aig.latchs.len();
        let num_constraints = aig.constraints.len();
        if aig.outputs.len() == 0 {
            aig.outputs.push(aig.bads[0]);
            aig.bads.clear();
        }
        let latchs = take(&mut aig.latchs);
        for l in latchs.iter() {
            aig.inputs.push(l.input);
            aig.outputs.push(l.next);
        }
        for c in take(&mut aig.constraints) {
            aig.outputs.push(c);
        }
        assert!(aig.inputs.len() == num_input + num_latchs);
        assert!(aig.outputs.len() == 1 + num_latchs + num_constraints);
        let mut abc = Abc::new();
        abc.read_aig(&aig);
        drop(aig);
        abc.execute_command("&get; &fraig -x; &put; rewrite; refactor");
        let mut abc_aig = abc.write_aig();
        for i in 0..num_latchs {
            let mut l = latchs[i];
            l.input = abc_aig.inputs[num_input + i];
            l.next = abc_aig.outputs[1 + i];
            abc_aig.latchs.push(l);
        }
        abc_aig.inputs.truncate(num_input);
        for i in 0..num_constraints {
            abc_aig
                .constraints
                .push(abc_aig.outputs[1 + num_latchs + i]);
        }
        abc_aig.outputs.truncate(1);

        assert!(abc_aig.inputs.len() == num_input);
        assert!(abc_aig.latchs.len() == num_latchs);
        assert!(abc_aig.constraints.len() == num_constraints);

        abc_aig
    }

    pub fn from_aig(aig: &Aig, strengthen: bool) -> (Self, AigRestore) {
        let (aig, mut remap) = aig.coi_refine();

        let mut remap_retain = HashSet::new();
        remap_retain.insert(AigEdge::constant_edge(false).node_id());
        for i in aig.inputs.iter() {
            remap_retain.insert(*i);
        }
        for l in aig.latchs.iter() {
            remap_retain.insert(l.input);
        }
        remap.retain(|x, _| remap_retain.contains(&x));
        let mut aig = Self::abc_preprocess(aig);
        aig.constraints
            .retain(|e| *e != AigEdge::constant_edge(true));

        let mut simp_solver: Box<dyn Satif> = if strengthen {
            Box::new(cadical::Solver::new())
        } else {
            Box::new(SimpSolver::new())
        };
        let false_lit: Lit = simp_solver.new_var().into();
        let mut dependence = VarMap::new();
        dependence.push(vec![]);
        simp_solver.add_clause(&[!false_lit]);
        for node in aig.nodes.iter().skip(1) {
            assert_eq!(Var::new(node.node_id()), simp_solver.new_var());
            let mut dep = Vec::new();
            if node.is_and() {
                dep.push(node.fanin0().to_lit().var());
                dep.push(node.fanin1().to_lit().var());
            }
            dependence.push(dep);
        }
        let inputs: Vec<Var> = aig.inputs.iter().map(|x| Var::new(*x)).collect();
        let latchs: Vec<Var> = aig.latchs.iter().map(|x| Var::new(x.input)).collect();
        let max_latch = *latchs.iter().max().unwrap();
        let mut latch_group = VarMap::new();
        latch_group.reserve(max_latch);
        let mut num_group = aig.latch_group.len() as u32;
        for l in aig.latchs.iter() {
            latch_group[Var::new(l.input)] = match aig.latch_group.get(&l.input) {
                Some(g) => *g,
                None => {
                    num_group += 1;
                    num_group - 1
                }
            }
        }
        let primes: Vec<Lit> = aig
            .latchs
            .iter()
            .map(|l| {
                dependence.push(vec![l.next.to_lit().var()]);
                simp_solver.new_var().lit()
            })
            .collect();
        let init = aig.latch_init_cube().to_cube();
        let mut init_map = HashMap::new();
        for l in init.iter() {
            init_map.insert(l.var(), l.polarity());
        }
        let constraints: Vec<Lit> = aig.constraints.iter().map(|c| c.to_lit()).collect();
        let aig_bad = if aig.bads.is_empty() {
            aig.outputs[0]
        } else {
            aig.bads[0]
        };
        for v in inputs.iter().chain(latchs.iter()) {
            simp_solver.set_frozen(*v, true);
        }
        for l in constraints.iter().chain(primes.iter()) {
            simp_solver.set_frozen(l.var(), true);
        }
        let mut logic = Vec::new();
        for l in aig.latchs.iter() {
            logic.push(l.next);
        }
        for c in aig.constraints.iter() {
            logic.push(*c);
        }
        logic.push(aig_bad);
        let mut trans = aig.get_cnf(&logic);
        for i in 0..aig.latchs.len() {
            trans.push(Clause::from([!primes[i], aig.latchs[i].next.to_lit()]));
            trans.push(Clause::from([primes[i], !aig.latchs[i].next.to_lit()]));
        }
        let bad = aig_bad.to_lit();
        simp_solver.set_frozen(bad.var(), true);
        for tran in trans.iter() {
            simp_solver.add_clause(tran);
        }
        simp_solver.simplify();
        let mut trans = simp_solver.clauses();
        let mut next_map = LitMap::new();
        for (l, p) in latchs.iter().zip(primes.iter()) {
            next_map.reserve(*l);
            let l = l.lit();
            next_map[l] = *p;
            next_map[!l] = !*p;
        }
        let mut domain = HashSet::new();
        for cls in trans.iter() {
            for l in cls.iter() {
                domain.insert(l.var());
            }
        }
        dependence = Self::compress_deps(dependence, &domain);
        for l in latchs.iter().chain(inputs.iter()) {
            domain.insert(*l);
        }
        let mut domain = Vec::from_iter(domain);
        domain.sort();
        let mut domain_map = HashMap::new();
        for (i, d) in domain.iter().enumerate() {
            domain_map.insert(*d, Var::new(i));
        }
        let map_lit = |l: Lit| Lit::new(domain_map[&l.var()], l.polarity());
        let inputs = inputs.into_iter().map(|v| domain_map[&v]).collect();
        let old_latchs = latchs.clone();
        let latchs: Vec<Var> = latchs.into_iter().map(|v| domain_map[&v]).collect();
        let primes: Vec<Lit> = primes.into_iter().map(map_lit).collect();
        let init = init.into_iter().map(map_lit).collect();
        let bad = map_lit(bad);
        let init_map = {
            let mut new = VarMap::new();
            for l in latchs.iter() {
                new.reserve(*l);
            }
            for (k, v) in init_map.iter() {
                new[domain_map[k]] = Some(*v);
            }
            new
        };
        let constraints = constraints.into_iter().map(map_lit).collect();
        for c in trans.iter_mut() {
            *c = c.iter().map(|l| map_lit(*l)).collect();
        }
        let num_var = domain.len();
        let mut next_map = LitMap::new();
        let mut prev_map = LitMap::new();
        for (l, p) in latchs.iter().zip(primes.iter()) {
            next_map.reserve(*l);
            prev_map.reserve(p.var());
            let l = l.lit();
            next_map[l] = *p;
            next_map[!l] = !*p;
            prev_map[*p] = l;
            prev_map[!*p] = !l;
        }
        let dependence = {
            let mut new = VarMap::new();
            for d in domain.iter() {
                let dep = dependence[*d].clone();
                let dep: Vec<Var> = dep.into_iter().map(|v| domain_map[&v]).collect();
                new.push(dep);
            }
            new
        };
        let max_latch = domain_map[&max_latch];
        let mut groups: HashMap<u32, Vec<Var>> = HashMap::new();
        let latch_group = {
            let mut new = VarMap::new();
            new.reserve(max_latch);
            for l in old_latchs.iter() {
                new[domain_map[l]] = latch_group[*l];
                let entry = groups.entry(latch_group[*l]).or_default();
                entry.push(domain_map[l]);
            }
            new
        };
        let mut is_latch = VarMap::new();
        is_latch.reserve(Var::new(num_var));
        for l in latchs.iter() {
            is_latch[*l] = true;
        }
        let mut restore = HashMap::new();
        for d in domain.iter() {
            if let Some(r) = remap.get(&(**d as _)) {
                restore.insert(domain_map[d], *r);
            }
        }
        (
            Self {
                inputs,
                latchs,
                init,
                bad,
                init_map,
                constraints,
                trans,
                num_var,
                is_latch,
                next_map,
                prev_map,
                dependence,
                max_latch,
                latch_group,
                groups,
            },
            AigRestore { restore },
        )
    }

    #[inline]
    pub fn new_var(&mut self) -> Var {
        let var = Var(self.num_var as _);
        self.num_var += 1;
        self.init_map.reserve(var);
        self.next_map.reserve(var);
        self.prev_map.reserve(var);
        self.is_latch.reserve(var);
        self.dependence.reserve(var);
        var
    }

    #[inline]
    pub fn add_latch(
        &mut self,
        state: Var,
        next: Lit,
        init: Option<bool>,
        trans: Vec<Clause>,
        dep: Vec<Var>,
    ) {
        assert!(dep.iter().all(|v| self.is_latch(*v)));
        self.latchs.push(state);
        let lit = state.lit();
        self.init_map[state] = init;
        self.is_latch[state] = true;
        self.next_map[lit] = next;
        self.next_map[!lit] = !next;
        self.prev_map[next] = lit;
        self.prev_map[!next] = !lit;
        if let Some(i) = init {
            self.init.push(lit.not_if(!i));
        }
        self.max_latch = self.max_latch.max(state);
        self.dependence[next.var()] = dep.iter().map(|v| self.next_map[v.lit()].var()).collect();
        self.dependence[state] = dep;
        for t in trans {
            self.trans.push(t);
        }
    }

    pub fn add_init(&mut self, v: Var, init: Option<bool>) {
        assert!(self.is_latch(v));
        self.init_map[v] = init;
        if let Some(i) = init {
            self.init.push(v.lit().not_if(!i));
        }
    }

    #[inline]
    pub fn lit_next(&self, lit: Lit) -> Lit {
        self.next_map[lit]
    }

    #[inline]
    pub fn lit_prev(&self, lit: Lit) -> Lit {
        self.prev_map[lit]
    }

    #[inline]
    pub fn cube_next(&self, cube: &[Lit]) -> Cube {
        cube.iter().map(|l| self.lit_next(*l)).collect()
    }

    #[inline]
    pub fn cube_subsume_init(&self, x: &[Lit]) -> bool {
        for x in x {
            if let Some(init) = self.init_map[x.var()] {
                if init != x.polarity() {
                    return false;
                }
            }
        }
        true
    }

    #[inline]
    pub fn is_latch(&self, var: Var) -> bool {
        self.is_latch[var]
    }

    pub fn get_coi(&self, var: impl Iterator<Item = Var>) -> Vec<Var> {
        let mut marked = HashSet::new();
        let mut queue = vec![];
        for v in var {
            marked.insert(v);
            queue.push(v);
        }
        while let Some(v) = queue.pop() {
            for d in self.dependence[v].iter() {
                if !marked.contains(d) {
                    marked.insert(*d);
                    queue.push(*d);
                }
            }
        }
        Vec::from_iter(marked.into_iter())
    }

    pub fn load_init(&self, satif: &mut impl Satif) {
        while satif.num_var() < self.num_var {
            satif.new_var();
        }
        for i in self.init.iter() {
            satif.add_clause(&[*i]);
        }
    }

    pub fn load_trans(&self, satif: &mut impl Satif) {
        while satif.num_var() < self.num_var {
            satif.new_var();
        }
        for c in self.trans.iter() {
            satif.add_clause(c);
        }
        for c in self.constraints.iter() {
            satif.add_clause(&[*c]);
        }
    }
}

#[derive(Debug)]
pub struct AigRestore {
    pub restore: HashMap<Var, usize>,
}

impl AigRestore {
    #[inline]
    pub fn restore(&self, lit: Lit) -> Lit {
        let var = Var::new(self.restore[&lit.var()]);
        Lit::new(var, lit.polarity())
    }
}

#[no_mangle]
pub extern "C" fn transys_from_aig(aig: *const c_char) -> *mut c_void {
    assert!(!aig.is_null());
    let aig = unsafe {
        let aig = CStr::from_ptr(aig);
        aig.to_string_lossy().into_owned()
    };
    let transys = Box::new(Transys::from_aig(&Aig::from_file(&aig), false).0);
    let ptr = transys.as_ref() as *const Transys as *mut c_void;
    forget(transys);
    ptr
}

#[no_mangle]
pub extern "C" fn transys_drop(transys: *mut c_void) {
    let transys: Box<Transys> = unsafe { Box::from_raw(transys as *mut _) };
    drop(transys)
}

#[no_mangle]
pub extern "C" fn transys_cube_subsume_init(
    transys: *mut c_void,
    lit_ptr: *const Lit,
    lit_len: u32,
) -> c_int {
    let transys = unsafe { &*(transys as *const Transys) };
    let cube = unsafe { from_raw_parts(lit_ptr, lit_len as _) };
    transys.cube_subsume_init(cube) as c_int
}

#[no_mangle]
pub extern "C" fn transys_lit_next(transys: *mut c_void, lit: c_uint) -> c_uint {
    let transys = unsafe { &*(transys as *const Transys) };
    unsafe { transmute(transys.lit_next(transmute::<u32, logic_form::Lit>(lit))) }
}
