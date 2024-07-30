use crate::Transys;
use logic_form::{Cube, Lit, LitMap, Var};
use satif::Satif;

pub struct TransysUnroll {
    pub ts: Transys,
    num_unroll: usize,
    pub num_var: usize,
    next_map: LitMap<Vec<Lit>>,
}

impl TransysUnroll {
    pub fn new(ts: &Transys) -> Self {
        let mut next_map: LitMap<Vec<_>> = LitMap::new();
        next_map.reserve(Var::new(ts.num_var));
        let false_lit = Lit::constant_lit(false);
        next_map[false_lit].push(false_lit);
        next_map[!false_lit].push(!false_lit);
        for v in 0..ts.num_var {
            let l = Var::new(v).lit();
            if next_map[l].is_empty() {
                next_map[l].push(l);
                next_map[!l].push(!l);
            }
        }
        for l in ts.latchs.iter() {
            let l = l.lit();
            let next = ts.lit_next(l);
            next_map[l].push(next);
            next_map[!l].push(!next);
        }
        Self {
            ts: ts.clone(),
            num_unroll: 0,
            num_var: ts.num_var,
            next_map,
        }
    }

    #[inline]
    pub fn lit_next(&self, lit: Lit, num: usize) -> Lit {
        self.next_map[lit][num]
    }

    #[inline]
    pub fn cube_next(&self, cube: &[Lit], num: usize) -> Cube {
        cube.iter().map(|l| self.lit_next(*l, num)).collect()
    }

    pub fn unroll(&mut self) {
        let false_lit = Lit::constant_lit(false);
        self.next_map[false_lit].push(false_lit);
        self.next_map[!false_lit].push(!false_lit);
        for v in 0..self.ts.num_var {
            let l = Var::new(v).lit();
            if self.next_map[l].len() == self.num_unroll + 1 {
                let new = Var::new(self.num_var).lit();
                self.num_var += 1;
                self.next_map[l].push(new);
                self.next_map[!l].push(!new);
            }
            assert!(self.next_map[l].len() == self.num_unroll + 2);
        }
        for l in self.ts.latchs.iter() {
            let l = l.lit();
            let next = self.lit_next(self.ts.lit_next(l), self.num_unroll + 1);
            self.next_map[l].push(next);
            self.next_map[!l].push(!next);
        }
        self.num_unroll += 1;
    }

    pub fn unroll_to(&mut self, k: usize) {
        while self.num_unroll < k {
            self.unroll()
        }
    }

    pub fn load_trans(&self, satif: &mut impl Satif, u: usize, constrain: bool) {
        while satif.num_var() < self.num_var {
            satif.new_var();
        }
        for c in self.ts.trans.iter() {
            let c: Vec<Lit> = c.iter().map(|l| self.lit_next(*l, u)).collect();
            satif.add_clause(&c);
        }
        if constrain {
            for c in self.ts.constraints.iter() {
                let c = self.lit_next(*c, u);
                satif.add_clause(&[c]);
            }
        }
    }

    // pub fn compile(&self) -> Transys {
    //     let mut inputs = Vec::new();
    //     let mut constraints = Vec::new();
    //     let mut trans = Cnf::new();
    //     for u in 0..=self.num_unroll {
    //         for i in self.ts.inputs.iter() {
    //             inputs.push(self.lit_next(i.lit(), u).var());
    //         }
    //         for c in self.ts.constraints.iter() {
    //             let c = self.lit_next(*c, u);
    //             constraints.push(c);
    //         }
    //         for c in self.ts.trans.iter() {
    //             let c: Clause = c.iter().map(|l| self.lit_next(*l, u)).collect();
    //             trans.push(c);
    //         }
    //     }
    //     let mut next_map = self.ts.next_map.clone();
    //     for l in self.ts.latchs.iter() {
    //         let l = l.lit();
    //         let n = self.lit_next(l, self.num_unroll);
    //         next_map[l] = n;
    //         next_map[!l] = !n;
    //     }
    //     let mut dependence = self.ts.dependence.clone();
    //     dependence.reserve(Var::new(self.num_var));
    //     for u in 1..=self.num_unroll {
    //         for i in 0..self.ts.num_var {
    //             let v = Var::new(i);
    //             let n = self.lit_next(v.lit(), u).var();
    //             if dependence[n].is_empty() {
    //                 dependence[n] = dependence[v]
    //                     .iter()
    //                     .map(|l| self.lit_next(l.lit(), u).var())
    //                     .collect()
    //             }
    //         }
    //     }
    //     Transys {
    //         inputs,
    //         latchs: self.ts.latchs.clone(),
    //         init: self.ts.init.clone(),
    //         bad: self.lit_next(self.ts.bad, 1),
    //         init_map: self.ts.init_map.clone(),
    //         constraints,
    //         trans,
    //         num_var: self.num_var,
    //         next_map,
    //         dependence,
    //         max_latch: self.ts.max_latch,
    //         latch_group: self.ts.latch_group.clone(),
    //     }
    // }

    // pub fn primed_constrains(&self) -> Transys {
    //     assert!(self.num_unroll == 1);
    //     let mut trans = Cnf::new();
    //     for u in 0..=1 {
    //         for c in self.ts.trans.iter() {
    //             let c: Clause = c.iter().map(|l| self.lit_next(*l, u)).collect();
    //             trans.push(c);
    //         }
    //     }
    //     let mut dependence = self.ts.dependence.clone();
    //     dependence.reserve(Var::new(self.num_var));
    //     let mut next_map = self.ts.next_map.clone();
    //     next_map.reserve(Var::new(self.num_var));
    //     for i in 0..self.ts.num_var {
    //         let l = Var::new(i).lit();
    //         next_map[l] = self.lit_next(l, 1);
    //         next_map[!l] = self.lit_next(!l, 1);
    //     }
    //     for i in 0..self.ts.num_var {
    //         let v = Var::new(i);
    //         let n = self.lit_next(v.lit(), 1).var();
    //         if dependence[n].is_empty() {
    //             dependence[n] = dependence[v]
    //                 .iter()
    //                 .map(|l| self.lit_next(l.lit(), 1).var())
    //                 .collect()
    //         }
    //     }
    //     Transys {
    //         inputs: self.ts.inputs.clone(),
    //         latchs: self.ts.latchs.clone(),
    //         init: self.ts.init.clone(),
    //         bad: self.ts.bad.clone(),
    //         init_map: self.ts.init_map.clone(),
    //         constraints: self.ts.constraints.clone(),
    //         trans,
    //         num_var: self.num_var,
    //         next_map,
    //         dependence,
    //         max_latch: self.ts.max_latch,
    //         latch_group: self.ts.latch_group.clone(),
    //     }
    // }

    // pub fn interal_signals(&self) -> Transys {
    //     assert!(self.num_unroll == 1);
    //     let mut trans = Cnf::new();
    //     for u in 0..=1 {
    //         for c in self.ts.trans.iter() {
    //             let c: Clause = c.iter().map(|l| self.lit_next(*l, u)).collect();
    //             trans.push(c);
    //         }
    //     }
    //     let mut dependence = self.ts.dependence.clone();
    //     dependence.reserve(Var::new(self.num_var));
    //     let mut next_map = self.ts.next_map.clone();
    //     next_map.reserve(Var::new(self.num_var));
    //     for i in 0..self.ts.num_var {
    //         let l = Var::new(i).lit();
    //         let n = self.lit_next(l, 1).var();
    //         next_map[l] = self.lit_next(l, 1);
    //         next_map[!l] = self.lit_next(!l, 1);
    //         if dependence[n].is_empty() {
    //             dependence[n] = dependence[l]
    //                 .iter()
    //                 .map(|l| self.lit_next(l.lit(), 1).var())
    //                 .collect()
    //         }
    //     }
    //     let mut keep: HashSet<Var> = HashSet::from_iter(self.ts.inputs.iter().cloned());
    //     for i in 0..self.ts.num_var {
    //         let v = Var::new(i);
    //         if dependence[v].iter().any(|d| keep.contains(d)) {
    //             keep.insert(v);
    //         }
    //     }
    //     let mut latchs = Vec::new();
    //     for i in 1..self.ts.num_var {
    //         let v = Var::new(i);
    //         if !keep.contains(&v) {
    //             latchs.push(v);
    //         }
    //     }
    //     let max_latch = *latchs.last().unwrap();
    //     let mut init_map = self.ts.init_map.clone();
    //     init_map.reserve(max_latch);
    //     let mut init = self.ts.init.clone();
    //     let mut solver = minisat::Solver::new();
    //     while solver.num_var() < self.num_var {
    //         solver.new_var();
    //     }
    //     for cls in trans.iter() {
    //         solver.add_clause(cls);
    //     }
    //     for c in self.ts.constraints.iter() {
    //         solver.add_clause(&[*c]);
    //     }
    //     let implies: HashSet<Lit> = HashSet::from_iter(solver.implies(&init).into_iter());
    //     for l in latchs.iter() {
    //         let l = l.lit();
    //         if implies.contains(&l) {
    //             init.push(l);
    //             init_map[l] = Some(true);
    //         } else if implies.contains(&!l) {
    //             init.push(!l);
    //             init_map[l] = Some(false);
    //         }
    //     }
    //     Transys {
    //         inputs: self.ts.inputs.clone(),
    //         latchs,
    //         init,
    //         bad: self.ts.bad.clone(),
    //         init_map,
    //         constraints: self.ts.constraints.clone(),
    //         trans,
    //         num_var: self.num_var,
    //         next_map,
    //         dependence,
    //         max_latch,
    //         latch_group: self.ts.latch_group.clone(),
    //     }
    // }
}
