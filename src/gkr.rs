use std::collections::HashSet;

use crate::graph::{Graph, GraphError, InputValue, Node};
use crate::sumcheck::SumCheck;
use ark_bn254::Fr as ScalarField;
use ark_ff::Zero;
use ark_poly::polynomial::multivariate::{SparsePolynomial, SparseTerm, Term};
use ark_poly::MVPolynomial;
use core::str::Chars;
use thiserror::Error;

#[derive(Error, Debug, PartialEq)]
pub enum GKRError {
    /// must generate trace first
    #[error("graph trace has not yet been generated")]
    TraceNotGenerated,
}

fn get_k(n: usize) -> usize {
    let mut k = 0;
    let mut m = n;
    while m > 1 {
        m >>= 1;
        k += 1;
    }
    if n & (n - 1) == 0 {
        k
    } else {
        k + 1
    }
}

pub struct Layer {
    pub k: usize,
    pub add: SparsePolynomial<ScalarField, SparseTerm>,
    pub mult: SparsePolynomial<ScalarField, SparseTerm>,
    pub wire: (Vec<Vec<ScalarField>>, Vec<Vec<ScalarField>>),
}

// Simulates memory of a single prover instance
#[derive(Debug, Clone)]
pub struct GKR<'a> {
    pub graph: Graph<'a>,
    pub sumcheck_proofs: Vec<SumCheck>,
}

impl<'a> GKR<'a> {
    pub fn new(nodes: Vec<&Node<'a>>, values: Vec<InputValue>) -> Result<Self, GraphError> {
        let mut graph = Graph::new(nodes)?;
        graph.forward(values)?;
        Ok(Self {
            graph,
            sumcheck_proofs: vec![],
        })
    }

    pub fn get_wiring_rep(&mut self, index: usize) -> Result<Layer, GKRError> {
        let layer_nodes = &self.graph.nodes[&index];
        let mut layer = Layer {
            k: get_k(layer_nodes.len()),
            add: SparsePolynomial::zero(),
            mult: SparsePolynomial::zero(),
            wire: (vec![], vec![]),
        };

        for (curr, node) in layer_nodes.iter().enumerate() {
            if let Node::Add { inputs, .. } | Node::Mult { inputs, .. } = node {
                let curr_string = format!("{:0k$b}", curr, k = layer.k);
                let prev_nodes = &self.graph.nodes[&(index - 1)];
                let prev_k = get_k(layer_nodes.len());
                let left_index = prev_nodes.iter().position(|&r| r == *inputs[0]).unwrap();
                let right_index = prev_nodes.iter().position(|&r| r == *inputs[1]).unwrap();
                let left_string = format!("{:0k$b}", left_index, k = prev_k);
                let right_string = format!("{:0k$b}", right_index, k = prev_k);
                let input = format!("{}{}{}", curr_string, left_string, right_string);
                let poly = polynomial_from_binary(input.chars());
                if let Node::Add { .. } = node {
                    layer.add = layer.add + poly;
                } else if let Node::Mult { .. } = node {
                    layer.mult = layer.mult + poly;
                }
            }
        }

        Ok(layer)
    }

    /// m_i
    pub fn sum_at_layer(&mut self, index: usize) -> Result<ScalarField, GKRError> {
        if self.graph.last_trace.len() == 0 {
            return Err(GKRError::TraceNotGenerated);
        }
        let mut sum = ScalarField::from(0);
        let level_nodes = &self.graph.nodes[&index];
        for node in level_nodes {
            sum += self.graph.last_trace[&node];
        }
        Ok(sum)
    }
}

pub fn polynomial_from_binary(input: Chars) -> SparsePolynomial<ScalarField, SparseTerm> {
    let mut terms: Vec<(ScalarField, SparseTerm)> = vec![];
    let unit = ScalarField::from(1);
    let num_vars = input.clone().count();
    for (idx, char) in input.enumerate() {
        // x_i
        if char == '1' {
            if terms.len() == 0 {
                terms.append(&mut vec![(unit, SparseTerm::new(vec![(idx, 1)]))])
            } else {
                for term in &mut terms {
                    let mut coeffs = (*term.1.clone()).to_vec();
                    coeffs.push((idx, 1));
                    term.1 = SparseTerm::new(coeffs);
                }
            }
        }
        // 1 - x_i
        else if char == '0' {
            if terms.len() == 0 {
                terms.append(&mut vec![
                    (unit, SparseTerm::new(vec![])),
                    (-unit, SparseTerm::new(vec![(idx, 1)])),
                ])
            } else {
                //  we check the original terms but push a new set of terms multiplied by -x_i
                let mut new_terms = vec![];
                for term in &terms {
                    let mut coeffs = (*term.1.clone()).to_vec();
                    coeffs.push((idx, 1));
                    new_terms.push((-term.0, SparseTerm::new(coeffs)));
                }
                terms.append(&mut new_terms);
            }
        }
    }

    SparsePolynomial::from_coefficients_vec(num_vars, terms)
}

#[cfg(test)]
mod tests {
    use ark_bn254::Fr as ScalarField;
    use ark_poly::{
        polynomial::multivariate::{SparsePolynomial, SparseTerm, Term},
        MVPolynomial,
    };

    #[test]
    pub fn test_poly_simplifies() {
        // Create a multivariate polynomial in 3 variables, with 4 terms:
        // 2*x_0^3 + x_0*x_2 +x_0*x_2   + x_1*x_2 + 5
        let poly1 = SparsePolynomial::from_coefficients_vec(
            3,
            vec![
                (ScalarField::from(2), SparseTerm::new(vec![(0, 3)])),
                (ScalarField::from(1), SparseTerm::new(vec![(0, 1), (2, 1)])),
                (ScalarField::from(1), SparseTerm::new(vec![(0, 1), (2, 1)])),
                (ScalarField::from(1), SparseTerm::new(vec![(1, 1), (2, 1)])),
                (ScalarField::from(5), SparseTerm::new(vec![])),
            ],
        );

        // Create a multivariate polynomial in 3 variables, with 4 terms:
        // 2*x_0^3 + 2*x_0*x_2   + x_1*x_2 + 5
        let poly2 = SparsePolynomial::from_coefficients_vec(
            3,
            vec![
                (ScalarField::from(2), SparseTerm::new(vec![(0, 3)])),
                (ScalarField::from(2), SparseTerm::new(vec![(0, 1), (2, 1)])),
                (ScalarField::from(1), SparseTerm::new(vec![(1, 1), (2, 1)])),
                (ScalarField::from(5), SparseTerm::new(vec![])),
            ],
        );
        assert_eq!(poly1, poly2);
    }
}
