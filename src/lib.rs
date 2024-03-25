use aig::Aig;
use logic_form::{Clause, Cnf, Cube, Lit, LitMap, Var, VarMap};
use minisat::SimpSolver;
use satif::Satif;
use std::{
    collections::{HashMap, HashSet},
    ffi::{c_char, c_int, c_uint, c_void, CStr},
    mem::{forget, transmute},
    slice::from_raw_parts,
    usize,
};

#[derive(Clone, Default)]
pub struct Transys {
    pub inputs: Vec<Var>,
    pub latchs: Vec<Var>,
    pub primes: Vec<Lit>,
    pub init: Cube,
    pub bad: Cube,
    pub init_map: HashMap<Var, bool>,
    pub constraints: Vec<Lit>,
    pub trans: Cnf,
    pub num_var: usize,
    next_map: LitMap<Lit>,
    pub dependence: VarMap<Vec<Var>>,
    pub max_latch: Var,
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

    fn compress_deps(mut deps: VarMap<Vec<Var>>, cnf: &Cnf) -> VarMap<Vec<Var>> {
        let mut domain = HashSet::new();
        for cls in cnf.iter() {
            for l in cls.iter() {
                domain.insert(l.var());
            }
        }
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

    pub fn from_aig(aig: &Aig) -> Self {
        let mut simp_solver = SimpSolver::new();
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
        let primes: Vec<Lit> = aig
            .latchs
            .iter()
            .map(|l| {
                dependence.push(vec![]);
                l.next.to_lit()
            })
            .collect();
        let init = aig.latch_init_cube().to_cube();
        let mut init_map = HashMap::new();
        for l in init.iter() {
            init_map.insert(l.var(), l.polarity());
        }
        let constraints: Vec<Lit> = aig.constraints.iter().map(|c| c.to_lit()).collect();
        assert!(constraints.is_empty());
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
        let trans = aig.get_cnf(&logic);
        let bad_lit = aig_bad.to_lit();
        let bad = Cube::from([bad_lit]);
        simp_solver.set_frozen(bad_lit.var(), true);
        for tran in trans.iter() {
            simp_solver.add_clause(tran);
        }
        for c in constraints.iter() {
            simp_solver.add_clause(&Clause::from([*c]));
        }
        simp_solver.eliminate(true);
        let num_var = simp_solver.num_var();
        let trans = simp_solver.clauses();
        let mut next_map = LitMap::new();
        for (l, p) in latchs.iter().zip(primes.iter()) {
            next_map.reserve(*l);
            let l = l.lit();
            next_map[l] = *p;
            next_map[!l] = !*p;
        }
        dependence = Self::compress_deps(dependence, &trans);
        Self {
            inputs,
            latchs,
            primes,
            init,
            bad,
            init_map,
            constraints,
            trans,
            num_var,
            next_map,
            dependence,
            max_latch,
        }
    }

    #[inline]
    pub fn lit_next(&self, lit: Lit) -> Lit {
        self.next_map[lit]
    }

    #[inline]
    pub fn cube_next(&self, cube: &[Lit]) -> Cube {
        cube.iter().map(|l| self.lit_next(*l)).collect()
    }

    #[inline]
    pub fn cube_subsume_init(&self, x: &[Lit]) -> bool {
        for x in x {
            if let Some(init) = self.init_map.get(&x.var()) {
                if *init != x.polarity() {
                    return false;
                }
            }
        }
        true
    }

    pub fn load_trans(&self, solver: &mut minisat::Solver) {
        while solver.num_var() < self.num_var {
            solver.new_var();
        }
        for cls in self.trans.iter() {
            solver.add_clause(cls)
        }
    }

    pub fn inits(&self) -> Vec<Cube> {
        self.init_map
            .iter()
            .map(|(latch, init)| Cube::from([Lit::new(*latch, !init)]))
            .collect()
    }
}

#[no_mangle]
pub extern "C" fn transys_from_aig(aig: *const c_char) -> *mut c_void {
    assert!(!aig.is_null());
    let aig = unsafe {
        let aig = CStr::from_ptr(aig);
        aig.to_string_lossy().into_owned()
    };
    let transys = Box::new(Transys::from_aig(&Aig::from_file(aig).unwrap()));
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
pub extern "C" fn transys_lit_next(transys: *mut c_void, lit: c_uint) -> c_uint {
    let transys = unsafe { &mut *(transys as *mut Transys) };
    unsafe { transmute(transys.lit_next(transmute(lit))) }
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
