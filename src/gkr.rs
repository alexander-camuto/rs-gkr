use crate::graph::{Graph, GraphError, InputValue, Node};
use crate::sumcheck::Prover as SumCheckProver;
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
}

#[cfg(test)]
mod tests {}
