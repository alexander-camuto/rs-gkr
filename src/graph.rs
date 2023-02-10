use crate::poly_utils::*;
use ark_bn254::Fr as ScalarField;
use ark_ff::Zero;
use ark_poly::polynomial::multivariate::SparsePolynomial;
use ark_poly::Polynomial;
use std::cmp::max;
use std::collections::HashMap;
use std::collections::{btree_map::Entry, BTreeMap, HashSet};
use thiserror::Error;

#[derive(Clone, Debug, PartialEq, Eq, Hash, Copy)]
pub struct InputValue {
    pub id: usize,
    pub value: ScalarField,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash, Copy)]
pub enum Node<'a> {
    Add {
        id: usize,
        inputs: [&'a Node<'a>; 2],
    },
    Mult {
        id: usize,
        inputs: [&'a Node<'a>; 2],
    },
    Input {
        id: usize,
    },
}

#[derive(Debug, PartialEq, Clone)]
pub enum MVLayer {
    OutputLayer {
        k: usize,
        add: MultiPoly,
        mult: MultiPoly,
        w_b: MultiPoly,
        w_c: MultiPoly,
        d: MultiPoly,
    },
    InterLayer {
        k: usize,
        add: MultiPoly,
        mult: MultiPoly,
        w_b: MultiPoly,
        w_c: MultiPoly,
    },
    InputLayer {
        k: usize,
        input_ext: MultiPoly,
    },
}

impl MVLayer {
    pub fn evaluation_ext(&self) -> MultiPoly {
        match self {
            Self::InputLayer { k: _, input_ext } => input_ext.clone(),
            Self::OutputLayer { d, .. } => d.clone(),
            Self::InterLayer { .. } => panic!(),
        }
    }

    pub fn w_ext_gate_eval(&self, r: &Vec<ScalarField>) -> MultiPoly {
        match self {
            Self::InputLayer { k: _, input_ext } => input_ext.clone(),
            Self::InterLayer {
                k: _,
                add,
                mult,
                w_b,
                w_c,
            }
            | Self::OutputLayer {
                k: _,
                add,
                mult,
                w_b,
                w_c,
                ..
            } => {
                let mut reduced_add_poly = mult_poly(&evaluate_variable(add, r), &(w_b + w_c));
                reduced_add_poly = neg_shift_poly_by_k(&reduced_add_poly, r.len());
                let mut reduced_mult_poly =
                    mult_poly(&evaluate_variable(mult, r), &mult_poly(&w_b, &w_c));
                reduced_mult_poly = neg_shift_poly_by_k(&reduced_mult_poly, r.len());
                reduced_add_poly + reduced_mult_poly
            }
        }
    }

    pub fn w_ext(&self) -> MultiPoly {
        match self {
            Self::InputLayer { k: _, input_ext } => input_ext.clone(),
            Self::InterLayer {
                k: _,
                add,
                mult,
                w_b,
                w_c,
            }
            | Self::OutputLayer {
                k: _,
                add,
                mult,
                w_b,
                w_c,
                ..
            } => mult_poly(add, &(w_b + w_c)) + mult_poly(mult, &mult_poly(&w_b, &w_c)),
        }
    }

    pub fn w_ext_line_restricted_values(
        &self,
        r: &Vec<ScalarField>,
        q0: ScalarField,
        q1: ScalarField,
    ) -> ScalarField {
        match self {
            Self::InputLayer { .. } => panic!(),
            Self::InterLayer { add, mult, .. } | Self::OutputLayer { add, mult, .. } => {
                add.evaluate(r) * (q0 + q1) + mult.evaluate(r) * (q0 * q1)
            }
        }
    }

    pub fn k(&self) -> usize {
        match self {
            Self::InputLayer { k, .. }
            | Self::InterLayer { k, .. }
            | Self::OutputLayer { k, .. } => *k,
        }
    }
}

#[derive(Error, Debug, PartialEq)]
pub enum GraphError {
    /// must generate trace first
    #[error("graph trace has not yet been generated")]
    TraceNotGenerated,
    /// node does not exist
    #[error("a queried node does not exist")]
    NodeExistence,
    /// node does not exist in trace
    #[error("a queried trace result does not exist")]
    TraceNodeExistence,
    /// inputs are of wrong length or an id mismatches
    #[error("bad inputs")]
    BadInputs,
    /// inputs
    #[error("a node that should be an input is not an input")]
    NonInput,
    /// graph format related error
    #[error("bad graph")]
    Format,
}

#[derive(Clone, Debug, PartialEq)]
pub struct Graph<'a> {
    pub nodes: BTreeMap<usize, Vec<Node<'a>>>,
    pub last_trace: HashMap<Node<'a>, ScalarField>,
    pub mv_layers: Vec<MVLayer>,
}

impl<'a> Graph<'a> {
    pub fn new(mut nodes: Vec<&Node<'a>>) -> Result<Self, GraphError> {
        // remove duplicates
        let mut seen = HashSet::new();
        nodes.retain(|item| seen.insert(*item));

        let mut graph = Self {
            nodes: BTreeMap::new(),
            last_trace: HashMap::new(),
            mv_layers: vec![],
        };

        // next step (we identify inputs)
        let mut labelled = false;
        while !labelled {
            labelled = true;
            for node in &nodes {
                if graph.get_level(node).is_err() {
                    match node {
                        Node::Input { .. } => {
                            graph.insert(0, node);
                        }
                        Node::Add { inputs, .. } | Node::Mult { inputs, .. } => {
                            if !nodes.contains(&inputs[0]) | !nodes.contains(&inputs[1]) {
                                return Err(GraphError::NodeExistence);
                            }
                            let first_level = graph.get_level(inputs[0]);
                            let second_level = graph.get_level(inputs[1]);
                            if first_level.is_err() || second_level.is_err() {
                                labelled = false;
                            } else {
                                // can safely unwrap as we checked for errors
                                let idx = max(first_level.unwrap(), second_level.unwrap()) + 1;
                                graph.insert(idx, node);
                            }
                        }
                    }
                }
            }
        }

        Ok(graph)
    }

    /// Insert the node with given idx
    fn insert(&mut self, idx: usize, node: &Node<'a>) {
        match self.nodes.entry(idx) {
            Entry::Vacant(e) => {
                e.insert(vec![node.clone()]);
            }
            Entry::Occupied(mut e) => {
                e.get_mut().push(node.clone());
            }
        }
    }

    /// Retrieves a node, as specified by idx, from the Graph of bucketed nodes.
    pub fn get_level(&self, node: &Node) -> Result<usize, GraphError> {
        let mut idx = None;
        for level in &self.nodes {
            if level.1.contains(&node) {
                idx = Some(level.0);
            }
        }
        match idx {
            None => Err(GraphError::NodeExistence),
            Some(i) => Ok(*i),
        }
    }

    /// Retrieves a node, as specified by idx, from the Graph of bucketed nodes.
    pub fn num_levels(&self) -> usize {
        self.nodes.len()
    }

    /// forward pass for a graph
    pub fn forward(&mut self, mut values: Vec<InputValue>) -> Result<(), GraphError> {
        // remove duplicates
        let mut seen = HashSet::new();
        values.retain(|item| seen.insert(*item));

        let mut trace: HashMap<Node<'a>, ScalarField> = HashMap::new();
        for input_node in &self.nodes[&0] {
            match input_node {
                Node::Input { id } => {
                    let relevant_input: Vec<&InputValue> =
                        values.iter().filter(|v| v.id == *id).collect();
                    if relevant_input.len() == 0 || relevant_input.len() > 1 {
                        return Err(GraphError::BadInputs);
                    } else {
                        trace.insert(*input_node, relevant_input[0].value);
                    }
                }
                _ => return Err(GraphError::NonInput),
            }
        }

        for i in 1..self.num_levels() {
            for op in &self.nodes[&i] {
                match op {
                    Node::Add { inputs, .. } => {
                        let first_input =
                            trace.get(inputs[0]).ok_or(GraphError::TraceNodeExistence)?;
                        let second_input =
                            trace.get(inputs[1]).ok_or(GraphError::TraceNodeExistence)?;
                        trace.insert(*op, *first_input + *second_input);
                    }
                    Node::Mult { inputs, .. } => {
                        let first_input =
                            trace.get(inputs[0]).ok_or(GraphError::TraceNodeExistence)?;
                        let second_input =
                            trace.get(inputs[1]).ok_or(GraphError::TraceNodeExistence)?;
                        trace.insert(*op, *first_input * *second_input);
                    }
                    _ => {}
                }
            }
        }
        self.last_trace = trace;

        Ok(())
    }

    pub fn get_multivariate_extension(&mut self) -> Result<(), GraphError> {
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

        if self.last_trace.len() == 0 {
            return Err(GraphError::TraceNotGenerated);
        }

        let mut layers: Vec<MVLayer> = vec![];
        for (index, layer_nodes) in &self.nodes {
            let k = get_k(layer_nodes.len());
            let layer = if index > &0 {
                let mut add_ext = SparsePolynomial::zero();
                let mut mult_ext = SparsePolynomial::zero();
                for (curr, node) in layer_nodes.iter().enumerate() {
                    if let Node::Add { inputs, .. } | Node::Mult { inputs, .. } = node {
                        // index of current node in layer as a binary string
                        let curr_string = format!("{:0k$b}", curr, k = k);
                        // get index of inbound nodes to the current gate
                        let prev_nodes = &self.nodes[&(index - 1)];
                        let prev_k = get_k(prev_nodes.len());
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
                            add_ext = add_ext + poly;
                        } else if let Node::Mult { .. } = node {
                            mult_ext = mult_ext + poly;
                        }
                    // input node
                    } else {
                        return Err(GraphError::Format);
                    }
                }

                let prev_layer = &layers[*index - 1];

                let w_b = shift_poly_by_k(&prev_layer.w_ext(), max(k, 1));
                let w_c = shift_poly_by_k(&prev_layer.w_ext(), prev_layer.k() + max(k, 1));
                if *index == &self.nodes.len() - 1 {
                    let output_poly = multilinear_polynomial_from_evals(
                        (0..layer_nodes.len()).collect(),
                        layer_nodes
                            .iter()
                            .map(|n| *self.last_trace.get(&n).unwrap())
                            .collect(),
                        k,
                    );
                    MVLayer::OutputLayer {
                        k: get_k(layer_nodes.len()),
                        add: add_ext,
                        mult: mult_ext,
                        w_b,
                        w_c,
                        d: output_poly,
                    }
                } else {
                    MVLayer::InterLayer {
                        k: get_k(layer_nodes.len()),
                        add: add_ext,
                        mult: mult_ext,
                        w_b,
                        w_c,
                    }
                }
            } else {
                let input_poly = multilinear_polynomial_from_evals(
                    (0..layer_nodes.len()).collect(),
                    layer_nodes
                        .iter()
                        .map(|n| *self.last_trace.get(&n).unwrap())
                        .collect(),
                    k,
                );
                MVLayer::InputLayer {
                    k: get_k(layer_nodes.len()),
                    input_ext: input_poly,
                }
            };
            layers.push(layer);
        }
        self.mv_layers = layers;
        Ok(())
    }
}

////////////////////////

#[cfg(test)]
mod tests {
    use super::*;

    use ark_poly::polynomial::multivariate::{SparsePolynomial, SparseTerm, Term};
    use ark_poly::DenseMVPolynomial;

    #[test]
    fn test_graph_init_add() {
        let first_input = Node::Input { id: 0 };
        let second_input = Node::Input { id: 1 };
        let third_input = Node::Input { id: 2 };
        let add_node = Node::Add {
            id: 0,
            inputs: [&first_input, &second_input],
        };
        let res = Graph::new(vec![&first_input, &second_input, &add_node]);
        assert!(res.is_ok());
        let mut graph = res.unwrap();

        assert_eq!(graph.get_level(&first_input).unwrap(), 0);
        assert_eq!(graph.get_level(&second_input).unwrap(), 0);
        assert_eq!(graph.get_level(&add_node).unwrap(), 1);
        assert_eq!(graph.nodes[&0].len(), 2);

        assert_eq!(
            graph.get_level(&third_input),
            Err(GraphError::NodeExistence)
        );

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

        assert_eq!(graph.last_trace[&first_input], ScalarField::from(1));
        assert_eq!(graph.last_trace[&second_input], ScalarField::from(2));
        assert_eq!(graph.last_trace[&add_node], ScalarField::from(3));

        let res = graph.forward(vec![InputValue {
            id: 0,
            value: ScalarField::from(1),
        }]);
        assert_eq!(res, Err(GraphError::BadInputs));

        let res = graph.forward(vec![
            InputValue {
                id: 0,
                value: ScalarField::from(1),
            },
            InputValue {
                id: 22,
                value: ScalarField::from(2),
            },
        ]);
        assert_eq!(res, Err(GraphError::BadInputs));
    }

    #[test]
    fn test_graph_init_mult() {
        let first_input = Node::Input { id: 0 };
        let second_input = Node::Input { id: 1 };
        let third_input = Node::Input { id: 2 };
        let mult_node = Node::Mult {
            id: 0,
            inputs: [&first_input, &second_input],
        };
        let res = Graph::new(vec![&first_input, &second_input, &mult_node]);
        assert!(res.is_ok());
        let mut graph = res.unwrap();

        assert_eq!(graph.get_level(&first_input).unwrap(), 0);
        assert_eq!(graph.get_level(&second_input).unwrap(), 0);
        assert_eq!(graph.get_level(&mult_node).unwrap(), 1);
        assert_eq!(graph.nodes[&0].len(), 2);

        assert_eq!(
            graph.get_level(&third_input),
            Err(GraphError::NodeExistence)
        );

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

        assert_eq!(graph.last_trace[&first_input], ScalarField::from(1));
        assert_eq!(graph.last_trace[&second_input], ScalarField::from(2));
        assert_eq!(graph.last_trace[&mult_node], ScalarField::from(2));

        let res = graph.forward(vec![InputValue {
            id: 0,
            value: ScalarField::from(1),
        }]);
        assert_eq!(res, Err(GraphError::BadInputs));

        let res = graph.forward(vec![
            InputValue {
                id: 0,
                value: ScalarField::from(1),
            },
            InputValue {
                id: 22,
                value: ScalarField::from(2),
            },
        ]);
        assert_eq!(res, Err(GraphError::BadInputs));
    }

    #[test]
    fn test_fails_if_not_in_init() {
        let first_input = Node::Input { id: 0 };
        let second_input = Node::Input { id: 1 };
        let third_input = Node::Input { id: 2 };
        let add_node = Node::Add {
            id: 0,
            inputs: [&first_input, &third_input],
        };
        let res = Graph::new(vec![&first_input, &second_input, &add_node]);

        assert_eq!(res, Err(GraphError::NodeExistence));
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

        let res = graph.get_multivariate_extension();
        assert!(res.is_ok());

        assert_eq!(
            graph.mv_layers[0],
            MVLayer::InputLayer {
                k: 1,
                input_ext: SparsePolynomial::from_coefficients_vec(
                    1,
                    vec![
                        (ScalarField::from(1), SparseTerm::new(vec![])),
                        (ScalarField::from(1), SparseTerm::new(vec![(0, 1)]))
                    ],
                )
            }
        );

        assert_eq!(
            graph.mv_layers[1],
            MVLayer::OutputLayer {
                k: 0,
                mult: SparsePolynomial::zero(),
                add: SparsePolynomial::from_coefficients_vec(
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
                ),
                w_b: shift_poly_by_k(&graph.mv_layers[0].evaluation_ext(), 1),
                w_c: shift_poly_by_k(&graph.mv_layers[0].evaluation_ext(), 2),
                d: SparsePolynomial::from_coefficients_vec(
                    1,
                    vec![
                        (ScalarField::from(-3), SparseTerm::new(vec![(0, 1)])),
                        (ScalarField::from(3), SparseTerm::new(vec![]))
                    ],
                ),
            }
        );
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

        let res = graph.get_multivariate_extension();
        assert!(res.is_ok());
        res.unwrap();

        assert_eq!(
            graph.mv_layers[0],
            MVLayer::InputLayer {
                k: 1,
                input_ext: SparsePolynomial::from_coefficients_vec(
                    1,
                    vec![
                        (ScalarField::from(1), SparseTerm::new(vec![])),
                        (ScalarField::from(1), SparseTerm::new(vec![(0, 1)]))
                    ],
                )
            }
        );

        assert_eq!(
            graph.mv_layers[1],
            MVLayer::OutputLayer {
                k: 0,
                add: SparsePolynomial::zero(),
                mult: SparsePolynomial::from_coefficients_vec(
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
                ),
                w_b: shift_poly_by_k(&graph.mv_layers[0].evaluation_ext(), 1),
                w_c: shift_poly_by_k(&graph.mv_layers[0].evaluation_ext(), 2),
                d: SparsePolynomial::from_coefficients_vec(
                    1,
                    vec![
                        (ScalarField::from(-2), SparseTerm::new(vec![(0, 1)])),
                        (ScalarField::from(2), SparseTerm::new(vec![]))
                    ],
                ),
            }
        );
    }

    #[test]
    fn test_graph_wiring_2_gate() {
        let first_input = Node::Input { id: 0 };
        let second_input = Node::Input { id: 1 };
        let add_node = Node::Add {
            id: 0,
            inputs: [&first_input, &second_input],
        };
        let mult_node = Node::Mult {
            id: 1,
            inputs: [&first_input, &second_input],
        };
        let res = Graph::new(vec![&first_input, &second_input, &add_node, &mult_node]);
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

        let res = graph.get_multivariate_extension();
        assert!(res.is_ok());

        assert_eq!(
            graph.mv_layers[0],
            MVLayer::InputLayer {
                k: 1,
                input_ext: SparsePolynomial::from_coefficients_vec(
                    1,
                    vec![
                        (ScalarField::from(1), SparseTerm::new(vec![])),
                        (ScalarField::from(1), SparseTerm::new(vec![(0, 1)]))
                    ],
                )
            }
        );

        assert_eq!(
            graph.mv_layers[1],
            MVLayer::OutputLayer {
                k: 1,
                mult: SparsePolynomial::from_coefficients_vec(
                    3,
                    vec![
                        (ScalarField::from(1), SparseTerm::new(vec![(0, 1), (2, 1)])),
                        (
                            ScalarField::from(-1),
                            SparseTerm::new(vec![(0, 1), (1, 1), (2, 1)])
                        )
                    ],
                ),
                add: SparsePolynomial::from_coefficients_vec(
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
                ),
                w_b: shift_poly_by_k(&graph.mv_layers[0].evaluation_ext(), 1),
                w_c: shift_poly_by_k(&graph.mv_layers[0].evaluation_ext(), 2),
                d: SparsePolynomial::from_coefficients_vec(
                    1,
                    vec![
                        (ScalarField::from(-1), SparseTerm::new(vec![(0, 1)])),
                        (ScalarField::from(3), SparseTerm::new(vec![]))
                    ],
                ),
            }
        );
    }
}
