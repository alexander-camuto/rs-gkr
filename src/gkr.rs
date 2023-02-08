use crate::graph::{Graph, GraphError, InputValue, Node};
use crate::sumcheck::SumCheck;
use ark_bn254::Fr as ScalarField;
use ark_ff::Zero;
use ark_poly::polynomial::multivariate::{SparsePolynomial, SparseTerm, Term};
use ark_poly::MVPolynomial;
use core::str::Chars;
use thiserror::Error;

pub type MultiPoly = SparsePolynomial<ScalarField, SparseTerm>;

#[derive(Error, Debug, PartialEq)]
pub enum GKRError {
    /// must generate trace first
    #[error("graph trace has not yet been generated")]
    TraceNotGenerated,
    /// graph related error
    #[error("graph error")]
    GraphError(GraphError),
    /// graph format related error
    #[error("bad graph")]
    GraphFormat,
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

#[derive(Debug, PartialEq, Clone)]
pub struct Layer {
    pub k: usize,
    pub add: MultiPoly,
    pub mult: MultiPoly,
    pub input: MultiPoly,
    pub wire: (Vec<Vec<ScalarField>>, Vec<Vec<ScalarField>>),
}

// Simulates memory of a single prover instance
#[derive(Debug, Clone)]
pub struct GKR {
    pub layers: Vec<Layer>,
    pub sumcheck_proofs: Vec<SumCheck>,
}

impl GKR {
    pub fn new<'a>(nodes: Vec<&Node<'a>>, values: Vec<InputValue>) -> Result<Self, GKRError> {
        let mut graph = Graph::new(nodes).map_err(|e| GKRError::GraphError(e))?;
        graph.forward(values).map_err(|e| GKRError::GraphError(e))?;
        Ok(Self {
            layers: get_wiring_rep(graph)?,
            sumcheck_proofs: vec![],
        })
    }
}

pub fn get_wiring_rep<'a>(graph: Graph<'a>) -> Result<Vec<Layer>, GKRError> {
    if graph.last_trace.len() == 0 {
        return Err(GKRError::TraceNotGenerated);
    }

    let mut layers = vec![];
    for (index, layer_nodes) in &graph.nodes {
        let mut layer = Layer {
            k: get_k(layer_nodes.len()),
            add: SparsePolynomial::zero(),
            mult: SparsePolynomial::zero(),
            input: SparsePolynomial::zero(),
            wire: (vec![], vec![]),
        };

        if index > &0 {
            for (curr, node) in layer_nodes.iter().enumerate() {
                if let Node::Add { inputs, .. } | Node::Mult { inputs, .. } = node {
                    // index of current node in layer as a binary string
                    let curr_string = format!("{:0k$b}", curr, k = layer.k);
                    // get index of inbound nodes to the current gate
                    let prev_nodes = &graph.nodes[&(index - 1)];
                    let prev_k = get_k(layer_nodes.len());
                    let left_index = prev_nodes.iter().position(|&r| r == *inputs[0]).unwrap();
                    let right_index = prev_nodes.iter().position(|&r| r == *inputs[1]).unwrap();

                    // wiring predicates as binary string
                    let left_string = format!("{:0k$b}", left_index, k = prev_k);
                    let right_string = format!("{:0k$b}", right_index, k = prev_k);
                    // total input as current node + inbound node 1 + inbound node 2
                    let input = format!("{}{}{}", curr_string, left_string, right_string);

                    let poly =
                        polynomial_from_binary(vec![input.chars()], vec![ScalarField::from(1)]);
                    if let Node::Add { .. } = node {
                        layer.add = layer.add + poly;
                    } else if let Node::Mult { .. } = node {
                        layer.mult = layer.mult + poly;
                    }
                // input node
                } else {
                    return Err(GKRError::GraphFormat);
                }
            }
        // input layer
        } else {
            let mut binary_inputs = vec![];
            let mut evals = vec![];
            for (curr, node) in layer_nodes.iter().enumerate() {
                if let Node::Input { .. } = node {
                    // index of current node in layer as a binary string
                    let curr_string = format!("{:0k$b}", curr, k = layer.k);
                    binary_inputs.push(curr_string);
                    evals.push(*graph.last_trace.get(&node).unwrap());
                } else {
                    return Err(GKRError::GraphFormat);
                }
            }
            let input: Vec<Chars> = binary_inputs.iter().map(|s| s.chars()).collect();
            let input_poly = polynomial_from_binary(input, evals);
            layer.input = input_poly;
        }
        layers.push(layer);
    }

    Ok(layers)
}

pub fn polynomial_from_binary(inputs: Vec<Chars>, evals: Vec<ScalarField>) -> MultiPoly {
    let mut terms: Vec<(ScalarField, SparseTerm)> = vec![];
    let num_vars = inputs.iter().map(|c| c.clone().count()).sum();
    // let mut offset = 0;
    for (input, unit) in inputs.iter().zip(evals) {
        let mut current_term: Vec<(ScalarField, SparseTerm)> = vec![];
        for (idx, char) in input.clone().enumerate() {
            // x_i
            if char == '1' {
                if current_term.len() == 0 {
                    current_term.append(&mut vec![(unit, SparseTerm::new(vec![(idx, 1)]))])
                } else {
                    for term in &mut current_term {
                        let mut coeffs = (*term.1.clone()).to_vec();
                        coeffs.push((idx, 1));
                        term.1 = SparseTerm::new(coeffs);
                    }
                }
            }
            // 1 - x_i
            else if char == '0' {
                if current_term.len() == 0 {
                    current_term.append(&mut vec![
                        (unit, SparseTerm::new(vec![])),
                        (-unit, SparseTerm::new(vec![(idx, 1)])),
                    ])
                } else {
                    //  we check the original terms but push a new set of terms multiplied by -x_i
                    let mut new_terms = vec![];
                    for term in &current_term {
                        let mut coeffs = (*term.1.clone()).to_vec();
                        coeffs.push((idx, 1));
                        new_terms.push((-term.0, SparseTerm::new(coeffs)));
                    }
                    current_term.append(&mut new_terms);
                }
            }
        }
        terms.append(&mut current_term)
    }

    SparsePolynomial::from_coefficients_vec(num_vars, terms)
}

#[cfg(test)]
mod tests {
    use super::*;
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

    #[test]
    pub fn test_poly_binary() {
        // Create a multivariate polynomial in 1 variable, with 1 term:
        // 1 - x_0
        let inputs = "0";
        let poly = polynomial_from_binary(vec![inputs.chars()], vec![ScalarField::from(1)]);
        let expected = SparsePolynomial::from_coefficients_vec(
            1,
            vec![
                (ScalarField::from(-1), SparseTerm::new(vec![(0, 1)])),
                (ScalarField::from(1), SparseTerm::new(vec![])),
            ],
        );
        assert_eq!(poly, expected);

        // Create a multivariate polynomial in 1 variable, with 1 term:
        // x_0
        let inputs = "1";
        let poly = polynomial_from_binary(vec![inputs.chars()], vec![ScalarField::from(1)]);
        let expected = SparsePolynomial::from_coefficients_vec(
            1,
            vec![(ScalarField::from(1), SparseTerm::new(vec![(0, 1)]))],
        );
        assert_eq!(poly, expected);

        // Create a multivariate polynomial in 2 variable, with 1 term:
        // x_0*x_1
        let inputs = "11";
        let poly = polynomial_from_binary(vec![inputs.chars()], vec![ScalarField::from(1)]);
        let expected = SparsePolynomial::from_coefficients_vec(
            2,
            vec![(ScalarField::from(1), SparseTerm::new(vec![(0, 1), (1, 1)]))],
        );
        assert_eq!(poly, expected);

        // Create a multivariate polynomial in 2 variable, with 2 terms:
        // -x_0*x_1 + x_1
        let inputs = "01";
        let poly = polynomial_from_binary(vec![inputs.chars()], vec![ScalarField::from(1)]);
        let expected = SparsePolynomial::from_coefficients_vec(
            2,
            vec![
                (ScalarField::from(-1), SparseTerm::new(vec![(0, 1), (1, 1)])),
                (ScalarField::from(1), SparseTerm::new(vec![(1, 1)])),
            ],
        );
        assert_eq!(poly, expected);

        // Create a multivariate polynomial in 2 variable, with 2 terms:
        // -x_0*x_1 + x_0
        let inputs = "10";
        let poly = polynomial_from_binary(vec![inputs.chars()], vec![ScalarField::from(1)]);
        let expected = SparsePolynomial::from_coefficients_vec(
            2,
            vec![
                (ScalarField::from(-1), SparseTerm::new(vec![(0, 1), (1, 1)])),
                (ScalarField::from(1), SparseTerm::new(vec![(0, 1)])),
            ],
        );
        assert_eq!(poly, expected);

        // Create a multivariate polynomial in 4 variable, with 2 terms:
        // -x_0*x_1*x_2*x_3 + x_0*x_2
        let inputs = "1011";
        let poly = polynomial_from_binary(vec![inputs.chars()], vec![ScalarField::from(1)]);
        let expected = SparsePolynomial::from_coefficients_vec(
            4,
            vec![
                (
                    ScalarField::from(-1),
                    SparseTerm::new(vec![(0, 1), (1, 1), (2, 1), (3, 1)]),
                ),
                (
                    ScalarField::from(1),
                    SparseTerm::new(vec![(0, 1), (2, 1), (3, 1)]),
                ),
            ],
        );
        assert_eq!(poly, expected);

        // Create a multivariate polynomial in 2 variable, with 2 term:
        // -x_0*x_1 + x_0
        let inputs = "1001";
        let poly = polynomial_from_binary(vec![inputs.chars()], vec![ScalarField::from(1)]);
        let expected = SparsePolynomial::from_coefficients_vec(
            4,
            vec![
                (
                    ScalarField::from(1),
                    SparseTerm::new(vec![(0, 1), (1, 1), (2, 1), (3, 1)]),
                ),
                (
                    ScalarField::from(-1),
                    SparseTerm::new(vec![(0, 1), (2, 1), (3, 1)]),
                ),
                (
                    ScalarField::from(-1),
                    SparseTerm::new(vec![(0, 1), (1, 1), (3, 1)]),
                ),
                (ScalarField::from(1), SparseTerm::new(vec![(0, 1), (3, 1)])),
            ],
        );
        assert_eq!(poly, expected);

        // Create a multivariate polynomial in 1 variable, with 1 term:
        // 1
        let inputs = vec!["0", "1"].iter().map(|c| c.chars()).collect();
        let evals = vec![ScalarField::from(1), ScalarField::from(1)];
        let poly = polynomial_from_binary(inputs, evals);
        let expected = SparsePolynomial::from_coefficients_vec(
            1,
            vec![(ScalarField::from(1), SparseTerm::new(vec![]))],
        );
        assert_eq!(poly, expected);

        // Create a multivariate polynomial in 2 variable, with 3 term:
        // 1 + x_1 + x_0*x_1
        let inputs = vec!["00", "01", "10", "11"]
            .iter()
            .map(|c| c.chars())
            .collect();
        let evals = vec![
            ScalarField::from(1),
            ScalarField::from(2),
            ScalarField::from(1),
            ScalarField::from(3),
        ];
        let poly = polynomial_from_binary(inputs, evals);
        let expected = SparsePolynomial::from_coefficients_vec(
            2,
            vec![
                (ScalarField::from(1), SparseTerm::new(vec![(0, 1), (1, 1)])),
                (ScalarField::from(1), SparseTerm::new(vec![(1, 1)])),
                (ScalarField::from(1), SparseTerm::new(vec![])),
            ],
        );
        assert_eq!(poly, expected);
    }

    #[test]
    fn test_graph_wiring_add() {
        let first_input = Node::Input { id: 0 };
        let second_input = Node::Input { id: 1 };
        let add_node = Node::Add {
            id: 0,
            inputs: [&first_input, &second_input],
        };
        let res = Graph::new(vec![&first_input, &second_input, &add_node]);
        assert!(res.is_ok());
        let mut graph = res.unwrap();
        let res = graph.forward(vec![
            InputValue {
                id: 0,
                value: ScalarField::from(1),
            },
            InputValue {
                id: 1,
                value: ScalarField::from(2),
            },
        ]);
        assert!(res.is_ok());

        let res = get_wiring_rep(graph);
        assert!(res.is_ok());
        let layers = res.unwrap();

        assert_eq!(layers[0].mult, SparsePolynomial::zero());
        assert_eq!(layers[0].add, SparsePolynomial::zero());
        assert_eq!(
            layers[0].input,
            SparsePolynomial::from_coefficients_vec(
                1,
                vec![
                    (ScalarField::from(1), SparseTerm::new(vec![])),
                    (ScalarField::from(1), SparseTerm::new(vec![(0, 1)]))
                ],
            )
        );

        assert_eq!(layers[1].mult, SparsePolynomial::zero());
        assert_eq!(
            layers[1].add,
            SparsePolynomial::from_coefficients_vec(
                3,
                vec![
                    (ScalarField::from(1), SparseTerm::new(vec![(2, 1)])),
                    (ScalarField::from(-1), SparseTerm::new(vec![(0, 1), (2, 1)])),
                    (ScalarField::from(-1), SparseTerm::new(vec![(1, 1), (2, 1)])),
                    (
                        ScalarField::from(1),
                        SparseTerm::new(vec![(0, 1), (1, 1), (2, 1)])
                    )
                ],
            )
        );
        assert_eq!(layers[1].input, SparsePolynomial::zero());
    }

    #[test]
    fn test_graph_wiring_mult() {
        let first_input = Node::Input { id: 0 };
        let second_input = Node::Input { id: 1 };
        let mult_node = Node::Mult {
            id: 0,
            inputs: [&first_input, &second_input],
        };
        let res = Graph::new(vec![&first_input, &second_input, &mult_node]);
        assert!(res.is_ok());
        let mut graph = res.unwrap();
        let res = graph.forward(vec![
            InputValue {
                id: 0,
                value: ScalarField::from(1),
            },
            InputValue {
                id: 1,
                value: ScalarField::from(2),
            },
        ]);
        assert!(res.is_ok());

        let res = get_wiring_rep(graph);
        assert!(res.is_ok());
        let layers = res.unwrap();

        assert_eq!(layers[0].add, SparsePolynomial::zero());
        assert_eq!(layers[0].mult, SparsePolynomial::zero());
        assert_eq!(
            layers[0].input,
            SparsePolynomial::from_coefficients_vec(
                1,
                vec![
                    (ScalarField::from(1), SparseTerm::new(vec![])),
                    (ScalarField::from(1), SparseTerm::new(vec![(0, 1)]))
                ],
            )
        );

        assert_eq!(layers[1].add, SparsePolynomial::zero());
        assert_eq!(
            layers[1].mult,
            SparsePolynomial::from_coefficients_vec(
                3,
                vec![
                    (ScalarField::from(1), SparseTerm::new(vec![(2, 1)])),
                    (ScalarField::from(-1), SparseTerm::new(vec![(0, 1), (2, 1)])),
                    (ScalarField::from(-1), SparseTerm::new(vec![(1, 1), (2, 1)])),
                    (
                        ScalarField::from(1),
                        SparseTerm::new(vec![(0, 1), (1, 1), (2, 1)])
                    )
                ],
            )
        );
        assert_eq!(layers[1].input, SparsePolynomial::zero());
    }
}
