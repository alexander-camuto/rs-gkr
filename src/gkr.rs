use crate::graph::{Graph, GraphError, InputValue, Node};
use crate::poly_utils::{restrict_poly_to_line, unique_univariate_line};
use crate::sumcheck::Prover as SumCheckProver;
use ark_bn254::Fr as ScalarField;
use ark_ff::Zero;
use ark_poly::DenseMVPolynomial;
use ark_poly::Polynomial;
use rand::Rng;
use std::cmp::max;
use thiserror::Error;

#[derive(Error, Debug, PartialEq)]
pub enum GKRError {
    /// graph related error
    #[error("graph error")]
    GraphError(GraphError),
}

// Simulates memory of a single prover instance
#[derive(Debug, Clone)]
pub struct Prover<'a> {
    pub graph: Graph<'a>,
    pub sumcheck_proofs: Vec<SumCheckProver>,
}

impl<'a> Prover<'a> {
    pub fn new(nodes: Vec<&Node<'a>>, values: Vec<InputValue>) -> Result<Self, GKRError> {
        let mut graph = Graph::new(nodes).map_err(|e| GKRError::GraphError(e))?;
        graph.forward(values).map_err(|e| GKRError::GraphError(e))?;
        graph
            .get_multivariate_extension()
            .map_err(|e| GKRError::GraphError(e))?;
        Ok(Self {
            graph,
            sumcheck_proofs: vec![],
        })
    }

    pub fn verify(&self) {
        // 1st round
        let last_layer = self.graph.mv_layers.last().unwrap();
        let mut r_i: Vec<ScalarField> = (0..max(last_layer.k(), 1)).map(|_| self.get_r()).collect();

        println!(
            "{:?} {:?}",
            r_i.len(),
            self.graph
                .mv_layers
                .last()
                .unwrap()
                .evaluation_ext()
                .num_vars(),
        );
        let mut m_i = self
            .graph
            .mv_layers
            .last()
            .unwrap()
            .evaluation_ext()
            .evaluate(&r_i);

        // recursive sumchecks
        for (idx, layer) in self.graph.mv_layers[1..].iter().enumerate().rev() {
            println!("{:?}", idx);
            let f_i = layer.w_ext_gate_eval(&r_i);
            let mut sumcheck_prover = SumCheckProver::new(&f_i);
            sumcheck_prover.verify(m_i);
            let prev_layer = &self.graph.mv_layers[idx - 1];
            let b = sumcheck_prover.r_vec[0..prev_layer.k()].to_vec();
            let c = sumcheck_prover.r_vec[prev_layer.k()..].to_vec();
            assert_eq!(b.len(), c.len());

            let lines = unique_univariate_line(&b, &c);

            assert_eq!(
                b,
                lines
                    .iter()
                    .map(|l| l.evaluate(&ScalarField::zero()))
                    .collect::<Vec<ScalarField>>()
            );

            assert_eq!(
                c,
                lines
                    .iter()
                    .map(|l| l.evaluate(&ScalarField::from(1)))
                    .collect::<Vec<ScalarField>>()
            );

            let restricted_poly = restrict_poly_to_line(prev_layer.w_ext(), &lines);

            assert_eq!(
                m_i,
                layer.w_ext_line_restricted_values(
                    &r_i,
                    restricted_poly.evaluate(&ScalarField::zero()),
                    restricted_poly.evaluate(&ScalarField::from(1))
                )
            );
            let r_star = self.get_r();
            r_i = lines.iter().map(|l| l.evaluate(&r_star)).collect();
            m_i = restricted_poly.evaluate(&r_star);
        }

        // final round
        let input_layer = self.graph.mv_layers.first().unwrap();
        assert_eq!(m_i, input_layer.w_ext().evaluate(&r_i));
    }

    // Verifier procedures
    pub fn get_r(&self) -> ScalarField {
        let mut rng = rand::thread_rng();
        rng.gen()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_proof_validates() {
        let first_input = Node::Input { id: 0 };
        let second_input = Node::Input { id: 1 };
        let add_node = Node::Add {
            id: 0,
            inputs: [&first_input, &second_input],
        };

        let res = Prover::new(
            vec![&first_input, &second_input, &add_node],
            vec![
                InputValue {
                    id: 0,
                    value: ScalarField::from(1),
                },
                InputValue {
                    id: 1,
                    value: ScalarField::from(2),
                },
            ],
        );
        assert!(res.is_ok());
        let prover = res.unwrap();

        prover.verify()
    }
}
