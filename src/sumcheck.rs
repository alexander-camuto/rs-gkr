use ark_bn254::Fr as ScalarField;
use ark_ff::Field;
use ark_poly::polynomial::multivariate::{SparsePolynomial, SparseTerm, Term};
use ark_poly::polynomial::univariate::SparsePolynomial as UniSparsePolynomial;
use ark_poly::{DenseMVPolynomial, Polynomial};
use rand::Rng;

pub type MultiPoly = SparsePolynomial<ScalarField, SparseTerm>;
pub type UniPoly = UniSparsePolynomial<ScalarField>;

// Converts i into an index in {0,1}^v
pub fn n_to_vec(i: usize, n: usize) -> Vec<ScalarField> {
    format!("{:0>width$}", format!("{:b}", i), width = n)
        .chars()
        .map(|x| if x == '1' { 1.into() } else { 0.into() })
        .collect()
}

// Simulates memory of a single prover instance
#[derive(Debug, Clone)]
pub struct Prover {
    pub g: MultiPoly,
    pub r_vec: Vec<ScalarField>,
}

impl Prover {
    pub fn new(g: &MultiPoly) -> Self {
        Prover {
            g: g.clone(),
            r_vec: vec![],
        }
    }

    // Given polynomial g, fix Xj, evaluate over xj+1
    pub fn gen_uni_polynomial(&mut self, r: Option<ScalarField>) -> UniPoly {
        if r.is_some() {
            self.r_vec.push(r.unwrap());
        }
        let v = self.g.num_vars() - self.r_vec.len();
        (0..(2u32.pow(v as u32 - 1))).fold(
            UniPoly::from_coefficients_vec(vec![(0, 0u32.into())]),
            |sum, n| sum + self.evaluate_gj(n_to_vec(n as usize, v)),
        )
    }
    // Evaluates gj over a vector permutation of points, folding all evaluated terms together into one univariate polynomial
    pub fn evaluate_gj(&self, points: Vec<ScalarField>) -> UniPoly {
        self.g.terms().iter().fold(
            UniPoly::from_coefficients_vec(vec![]),
            |sum, (coeff, term)| {
                let (coeff_eval, fixed_term) = self.evaluate_term(&term, &points);
                let curr = match fixed_term {
                    None => UniPoly::from_coefficients_vec(vec![(0, *coeff * coeff_eval)]),
                    _ => UniPoly::from_coefficients_vec(vec![(
                        fixed_term.unwrap().degree(),
                        *coeff * coeff_eval,
                    )]),
                };
                curr + sum
            },
        )
    }

    // Evaluates a term with a fixed univar, returning (new coefficent, fixed term)
    pub fn evaluate_term(
        &self,
        term: &SparseTerm,
        point: &Vec<ScalarField>,
    ) -> (ScalarField, Option<SparseTerm>) {
        let mut fixed_term: Option<SparseTerm> = None;
        let coeff: ScalarField =
            term.iter()
                .fold(1u32.into(), |product, (var, power)| match *var {
                    j if j == self.r_vec.len() => {
                        fixed_term = Some(SparseTerm::new(vec![(j, *power)]));
                        product
                    }
                    j if j < self.r_vec.len() => self.r_vec[j].pow(&[*power as u64]) * product,
                    _ => point[*var - self.r_vec.len()].pow(&[*power as u64]) * product,
                });
        (coeff, fixed_term)
    }

    // Sum all evaluations of polynomial `g` over boolean hypercube
    pub fn slow_sum_g(&self) -> ScalarField {
        let v = self.g.num_vars();
        let n = 2u32.pow(v as u32);
        (0..n)
            .map(|n| self.g.evaluate(&n_to_vec(n as usize, v)))
            .sum()
    }

    // Verify prover's claim c_1
    // Presented pedantically:
    pub fn verify(&mut self, c_1: ScalarField) -> bool {
        // 1st round
        let mut gi = self.gen_uni_polynomial(None);
        let mut expected_c = gi.evaluate(&0u32.into()) + gi.evaluate(&1u32.into());
        assert_eq!(c_1, expected_c);
        let lookup_degree = max_degrees(&self.g);
        assert!(gi.degree() <= lookup_degree[0]);

        // middle rounds
        for j in 1..self.g.num_vars() {
            let r = self.get_r();
            expected_c = gi.evaluate(&r.unwrap());
            gi = self.gen_uni_polynomial(r);
            let new_c = gi.evaluate(&0u32.into()) + gi.evaluate(&1u32.into());
            assert_eq!(expected_c, new_c);
            assert!(gi.degree() <= lookup_degree[j]);
        }
        // final round
        let r = self.get_r();
        expected_c = gi.evaluate(&r.unwrap());
        self.r_vec.push(r.unwrap());
        let new_c = self.g.evaluate(&self.r_vec);
        assert_eq!(expected_c, new_c);
        true
    }
    // Verifier procedures
    pub fn get_r(&self) -> Option<ScalarField> {
        let mut rng = rand::thread_rng();
        let r: ScalarField = rng.gen();
        Some(r)
    }
}

// A degree look up table for all variables in g
pub fn max_degrees(g: &MultiPoly) -> Vec<usize> {
    let mut lookup: Vec<usize> = vec![0; g.num_vars()];
    g.terms().iter().for_each(|(_, term)| {
        term.iter().for_each(|(var, power)| {
            if *power > lookup[*var] {
                lookup[*var] = *power
            }
        });
    });
    lookup
}
