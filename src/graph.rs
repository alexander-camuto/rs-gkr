use std::cmp::max;
use std::collections::HashMap;
use std::collections::{btree_map::Entry, BTreeMap, HashSet};
use thiserror::Error;

#[derive(Clone, Debug, PartialEq, Eq, Hash, Copy)]
pub struct InputValue {
    id: usize,
    value: usize,
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

#[derive(Error, Debug, PartialEq)]
pub enum GraphError {
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
}

#[derive(Clone, Debug, PartialEq)]
pub struct Graph<'a> {
    nodes: BTreeMap<usize, Vec<Node<'a>>>,
    last_trace: HashMap<Node<'a>, usize>,
}

impl<'a> Graph<'a> {
    pub fn new(mut nodes: Vec<&Node<'a>>) -> Result<Self, GraphError> {
        // remove duplicates
        let set: HashSet<_> = nodes.drain(..).collect(); // dedup
        nodes = set.into_iter().collect();

        print!("{:?}", nodes);

        let mut graph = Self {
            nodes: BTreeMap::new(),
            last_trace: HashMap::new(),
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
        let set: HashSet<_> = values.drain(..).collect(); // dedup
        values = set.into_iter().collect();

        let mut trace: HashMap<Node<'a>, usize> = HashMap::new();
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
                        trace.insert(*op, first_input + second_input);
                    }
                    Node::Mult { inputs, .. } => {
                        let first_input =
                            trace.get(inputs[0]).ok_or(GraphError::TraceNodeExistence)?;
                        let second_input =
                            trace.get(inputs[1]).ok_or(GraphError::TraceNodeExistence)?;
                        trace.insert(*op, first_input * second_input);
                    }
                    _ => {}
                }
            }
        }
        self.last_trace = trace;

        Ok(())
    }
}

////////////////////////

#[cfg(test)]
mod tests {
    use super::*;

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
            InputValue { id: 0, value: 1 },
            InputValue { id: 1, value: 2 },
        ]);
        assert!(res.is_ok());

        assert_eq!(graph.last_trace[&first_input], 1);
        assert_eq!(graph.last_trace[&second_input], 2);
        assert_eq!(graph.last_trace[&add_node], 3);

        let res = graph.forward(vec![InputValue { id: 0, value: 1 }]);
        assert_eq!(res, Err(GraphError::BadInputs));

        let res = graph.forward(vec![
            InputValue { id: 0, value: 1 },
            InputValue { id: 22, value: 2 },
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
            InputValue { id: 0, value: 1 },
            InputValue { id: 1, value: 2 },
        ]);
        assert!(res.is_ok());

        assert_eq!(graph.last_trace[&first_input], 1);
        assert_eq!(graph.last_trace[&second_input], 2);
        assert_eq!(graph.last_trace[&mult_node], 2);

        let res = graph.forward(vec![InputValue { id: 0, value: 1 }]);
        assert_eq!(res, Err(GraphError::BadInputs));

        let res = graph.forward(vec![
            InputValue { id: 0, value: 1 },
            InputValue { id: 22, value: 2 },
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
}
