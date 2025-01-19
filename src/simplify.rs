use super::Transys;
use logic_form::{Clause, Lit, Var, VarMap};
use satif::Satif;
use satif_minisat::SimpSolver;
use std::collections::HashSet;

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
            Self::compress_deps_rec(v, &mut deps, domain, &mut compressed)
        }
        for v in 0..deps.len() {
            let v = Var::new(v);
            if !domain.contains(&v) {
                deps[v].clear();
            }
        }
        deps
    }

    pub fn simplify(&self, lemmas: &[Clause], keep_dep: bool, assert_constrain: bool) -> Self {
        assert!(!assert_constrain);
        let mut simp_solver: Box<dyn Satif> = if keep_dep {
            Box::new(SimpSolver::new())
        } else {
            Box::new(satif_cadical::Solver::new())
        };
        let false_lit: Lit = simp_solver.new_var().into();
        simp_solver.add_clause(&[!false_lit]);
        simp_solver.new_var_to(self.max_var);
        for c in self.trans.iter().chain(lemmas.iter()) {
            simp_solver.add_clause(c);
        }
        let mut frozens = Vec::new();
        for i in self.inputs.iter() {
            frozens.push(*i);
        }
        for l in self.latchs.iter() {
            frozens.push(*l);
            frozens.push(self.var_next(*l))
        }
        frozens.push(self.bad.var());
        for c in self.constraints.iter() {
            if assert_constrain {
                simp_solver.add_clause(&[*c]);
            } else {
                frozens.push(c.var());
            }
        }
        for f in frozens.iter() {
            simp_solver.set_frozen(*f, true);
        }
        if let Some(false) = simp_solver.simplify() {
            println!("warning: model trans simplified with unsat");
        }
        let mut trans = simp_solver.clauses();
        trans.push(Clause::from([!false_lit]));
        let mut max_var = false_lit.var();
        let mut domain = HashSet::from_iter(frozens);
        max_var = *domain.iter().max().unwrap_or(&max_var);
        for cls in trans.iter() {
            for l in cls.iter() {
                domain.insert(l.var());
            }
        }
        max_var = *domain.iter().max().unwrap_or(&max_var);
        for l in self.latchs.iter().chain(self.inputs.iter()) {
            domain.insert(*l);
        }
        let dep = Self::compress_deps(self.dependence.clone(), &domain);
        Self {
            inputs: self.inputs.clone(),
            latchs: self.latchs.clone(),
            init: self.init.clone(),
            bad: self.bad,
            init_map: self.init_map.clone(),
            constraints: self.constraints.clone(),
            trans,
            max_var,
            is_latch: self.is_latch.clone(),
            next_map: self.next_map.clone(),
            prev_map: self.prev_map.clone(),
            dependence: dep,
            max_latch: self.max_latch,
            restore: self.restore.clone(),
        }
    }
}
