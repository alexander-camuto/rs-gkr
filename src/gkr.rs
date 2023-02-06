use crate::graph::{Graph, GraphError, InputValue, Node};
use crate::sumcheck::SumCheck;
use ark_bn254::Fr as ScalarField;
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
    pub add: Vec<Vec<ScalarField>>,
    pub mult: Vec<Vec<ScalarField>>,
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
            add: vec![],
            mult: vec![],
            wire: (vec![], vec![]),
        };

        let add_nodes: Vec<(usize, &Node)> = layer_nodes
            .iter()
            .enumerate()
            .filter(|(_, node)| match **node {
                Node::Add { .. } => true,
                _ => false,
            })
            .collect();

        let mult_nodes: Vec<(usize, &Node)> = layer_nodes
            .iter()
            .enumerate()
            .filter(|(_, node)| match **node {
                Node::Mult { .. } => true,
                _ => false,
            })
            .collect();

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
