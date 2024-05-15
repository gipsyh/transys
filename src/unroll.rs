use crate::Transys;
use logic_form::{Cube, Lit, LitMap, Var};
use satif::Satif;

pub struct TransysUnroll {
    ts: Transys,
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

    pub fn load_trans(&self, satif: &mut impl Satif) {
        while satif.num_var() < self.num_var {
            satif.new_var();
        }
        for u in 0..=self.num_unroll {
            for c in self.ts.trans.iter() {
                let c: Vec<Lit> = c.iter().map(|l| self.lit_next(*l, u)).collect();
                satif.add_clause(&c);
            }
            for c in self.ts.constraints.iter() {
                let c = self.lit_next(*c, u);
                satif.add_clause(&[c]);
            }
        }
    }
}
