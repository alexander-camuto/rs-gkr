use ark_bn254::Fr as ScalarField;
use ark_ff::Zero;
use ark_poly::polynomial::multivariate::{SparsePolynomial, SparseTerm, Term};
use ark_poly::polynomial::univariate::SparsePolynomial as UniSparsePolynomial;
use ark_poly::DenseMVPolynomial;
use core::str::Chars;
use std::cmp::max;

pub type MultiPoly = SparsePolynomial<ScalarField, SparseTerm>;
pub type UniPoly = UniSparsePolynomial<ScalarField>;

pub fn evaluate_variable(p: &MultiPoly, r: &Vec<ScalarField>) -> MultiPoly {
    if p.is_zero() {
        return p.clone();
    }
    let mut new_coefficients = vec![];
    let new_num_vars = p.num_vars();
    for (unit, term) in p.terms() {
        let mut new_unit = *unit;
        let mut new_term = vec![];
        for (var, power) in (*term).iter() {
            if var < &r.len() {
                for _ in 0..*power {
                    new_unit = new_unit * r[*var];
                }
            } else {
                new_term.push((*var, *power));
            }
        }
        new_coefficients.push((new_unit, SparseTerm::new(new_term)));
    }
    MultiPoly::from_coefficients_vec(new_num_vars, new_coefficients)
}

pub fn restrict_poly_to_line(p: MultiPoly, line: &[UniPoly]) -> UniPoly {
    let mut restricted_poly = UniPoly::zero();
    for (unit, term) in p.terms() {
        let variables: Vec<_> = (*term).to_vec();
        let mut term_poly = UniPoly::from_coefficients_slice(&[(0, *unit)]);
        for (var, power) in variables {
            let mut var_poly = line[var].clone();
            for _ in 0..(power - 1) {
                var_poly = var_poly.mul(&var_poly)
            }
            term_poly = term_poly.mul(&var_poly);
        }
        restricted_poly = restricted_poly + term_poly;
    }
    restricted_poly
}

pub fn unique_univariate_line(b: &[ScalarField], c: &[ScalarField]) -> Vec<UniPoly> {
    let mut lines = vec![];
    for (b_i, c_i) in b.iter().zip(c) {
        lines.push(UniPoly::from_coefficients_slice(&[
            (0, *b_i),
            (1, c_i - b_i),
        ]));
    }
    lines
}

pub fn mult_poly(p1: &MultiPoly, p2: &MultiPoly) -> MultiPoly {
    let p1_terms = p1.terms();
    let p2_terms = p2.terms();
    let num_vars = max(p1.num_vars(), p2.num_vars());
    let mut mult_terms = vec![];
    for (unit_1, term_1) in p1_terms {
        for (unit_2, term_2) in p2_terms {
            let mut mult_term: Vec<_> = (*term_1).to_vec();
            mult_term.append(&mut term_2.to_vec());
            mult_terms.push((unit_1 * unit_2, SparseTerm::new(mult_term)));
        }
    }
    MultiPoly::from_coefficients_vec(num_vars, mult_terms)
}

pub fn mult_poly_by_scalar(s: &ScalarField, p: &MultiPoly) -> MultiPoly {
    let terms = p.terms();
    let mut mult_terms = vec![];
    for (unit, term) in terms {
        mult_terms.push((unit * s, term.clone()));
    }
    MultiPoly::from_coefficients_vec(p.num_vars(), mult_terms)
}

pub fn shift_poly_by_k(p: &MultiPoly, k: usize) -> MultiPoly {
    let terms = p.terms();
    let current_num_vars = p.num_vars();
    let mut shifted_terms = vec![];
    for (unit, term) in terms {
        let shifted_term = SparseTerm::new((*term).iter().map(|c| (c.0 + k, c.1)).collect());
        shifted_terms.push((*unit, shifted_term));
    }
    MultiPoly::from_coefficients_vec(current_num_vars + k, shifted_terms)
}

pub fn multilinear_polynomial_from_evals(
    inputs: Vec<usize>,
    evals: Vec<ScalarField>,
    k: usize,
) -> MultiPoly {
    let mut binary_inputs = vec![];
    for curr in inputs {
        // index of current node in layer as a binary string
        let curr_string = format!("{:0k$b}", curr, k = k);
        binary_inputs.push(curr_string);
    }
    let input: Vec<Chars> = binary_inputs.iter().map(|s| s.chars()).collect();
    polynomial_from_binary(input, evals)
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

    MultiPoly::from_coefficients_vec(num_vars, terms)
}

#[cfg(test)]
mod tests {
    use super::*;
    use ark_bn254::Fr as ScalarField;
    use ark_poly::{
        polynomial::multivariate::{SparseTerm, Term},
        DenseMVPolynomial,
    };

    #[test]
    pub fn test_poly_simplifies() {
        // Create a multivariate polynomial in 3 variables, with 4 terms:
        // 2*x_0^3 + x_0*x_2 +x_0*x_2   + x_1*x_2 + 5
        let poly1 = MultiPoly::from_coefficients_vec(
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
        let poly2 = MultiPoly::from_coefficients_vec(
            3,
            vec![
                (ScalarField::from(2), SparseTerm::new(vec![(0, 3)])),
                (ScalarField::from(2), SparseTerm::new(vec![(0, 1), (2, 1)])),
                (ScalarField::from(1), SparseTerm::new(vec![(1, 1), (2, 1)])),
                (ScalarField::from(5), SparseTerm::new(vec![])),
            ],
        );
        assert_eq!(poly1, poly2);

        // Create a multivariate polynomial in 3 variables, with 4 terms:
        // 2*x_0^3 + x_0*x_2 +x_0*x_2   + x_1*x_2 + 5
        let poly1 = MultiPoly::from_coefficients_vec(
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
        let poly2 = MultiPoly::from_coefficients_vec(
            3,
            vec![
                (
                    ScalarField::from(2),
                    SparseTerm::new(vec![(0, 1), (0, 1), (0, 1)]),
                ),
                (ScalarField::from(2), SparseTerm::new(vec![(0, 1), (2, 1)])),
                (ScalarField::from(1), SparseTerm::new(vec![(1, 1), (2, 1)])),
                (ScalarField::from(5), SparseTerm::new(vec![])),
            ],
        );
        assert_eq!(poly1, poly2);
    }

    #[test]
    pub fn test_poly_shift() {
        // Create a multivariate polynomial in 3 variables, with 4 terms:
        // 2*x_0^3 + x_0*x_2 +x_0*x_2   + x_1*x_2 + 5
        let poly1 = MultiPoly::from_coefficients_vec(
            3,
            vec![
                (ScalarField::from(2), SparseTerm::new(vec![(0, 3)])),
                (ScalarField::from(1), SparseTerm::new(vec![(0, 1), (2, 1)])),
                (ScalarField::from(1), SparseTerm::new(vec![(0, 1), (2, 1)])),
                (ScalarField::from(1), SparseTerm::new(vec![(1, 1), (2, 1)])),
                (ScalarField::from(5), SparseTerm::new(vec![])),
            ],
        );

        let poly2 = shift_poly_by_k(&poly1, 3);

        assert_eq!(
            poly2,
            MultiPoly::from_coefficients_vec(
                6,
                vec![
                    (ScalarField::from(2), SparseTerm::new(vec![(3, 3)])),
                    (ScalarField::from(1), SparseTerm::new(vec![(3, 1), (5, 1)])),
                    (ScalarField::from(1), SparseTerm::new(vec![(3, 1), (5, 1)])),
                    (ScalarField::from(1), SparseTerm::new(vec![(4, 1), (5, 1)])),
                    (ScalarField::from(5), SparseTerm::new(vec![])),
                ],
            )
        );

        // Create a multivariate polynomial in 3 variables, with 4 terms:
        // 2*x_0^3 + 2*x_0*x_2   + x_1*x_2 + 5
        let poly1 = MultiPoly::from_coefficients_vec(
            3,
            vec![
                (ScalarField::from(2), SparseTerm::new(vec![(0, 3)])),
                (ScalarField::from(2), SparseTerm::new(vec![(0, 1), (2, 1)])),
                (ScalarField::from(1), SparseTerm::new(vec![(1, 1), (2, 1)])),
                (ScalarField::from(5), SparseTerm::new(vec![])),
            ],
        );
        let poly2 = shift_poly_by_k(&poly1, 3);
        assert_eq!(
            poly2,
            MultiPoly::from_coefficients_vec(
                6,
                vec![
                    (ScalarField::from(2), SparseTerm::new(vec![(3, 3)])),
                    (ScalarField::from(2), SparseTerm::new(vec![(3, 1), (5, 1)])),
                    (ScalarField::from(1), SparseTerm::new(vec![(4, 1), (5, 1)])),
                    (ScalarField::from(5), SparseTerm::new(vec![])),
                ],
            )
        );
    }

    #[test]
    pub fn test_poly_mult() {
        // Create a multivariate polynomial in 3 variables, with 4 terms:
        // 2*x_0^3 + x_0*x_2 +x_0*x_2   + x_1*x_2 + 5
        let poly1 = MultiPoly::from_coefficients_vec(
            1,
            vec![
                (ScalarField::from(2), SparseTerm::new(vec![(0, 3)])),
                (ScalarField::from(5), SparseTerm::new(vec![])),
            ],
        );

        let poly2 = MultiPoly::from_coefficients_vec(
            4,
            vec![
                (ScalarField::from(2), SparseTerm::new(vec![(3, 3)])),
                (ScalarField::from(5), SparseTerm::new(vec![])),
            ],
        );

        let mult_poly = mult_poly(&poly1, &poly2);

        assert_eq!(mult_poly.num_vars(), 4);
        assert_eq!(
            mult_poly,
            MultiPoly::from_coefficients_vec(
                6,
                vec![
                    (ScalarField::from(10), SparseTerm::new(vec![(0, 3)])),
                    (ScalarField::from(10), SparseTerm::new(vec![(3, 3)])),
                    (ScalarField::from(4), SparseTerm::new(vec![(0, 3), (3, 3)])),
                    (ScalarField::from(25), SparseTerm::new(vec![])),
                ],
            )
        );
    }

    #[test]
    pub fn test_poly_ml_from_evals() {
        // Create a multivariate polynomial in 1 variable, with 1 term:
        // 1 - x_0
        let inputs = vec![0];
        let poly = multilinear_polynomial_from_evals(inputs, vec![ScalarField::from(1)], 1);
        let expected = MultiPoly::from_coefficients_vec(
            1,
            vec![
                (ScalarField::from(-1), SparseTerm::new(vec![(0, 1)])),
                (ScalarField::from(1), SparseTerm::new(vec![])),
            ],
        );
        assert_eq!(poly, expected);

        // Create a multivariate polynomial in 1 variable, with 1 term:
        // x_0
        let inputs = vec![1];
        let poly = multilinear_polynomial_from_evals(inputs, vec![ScalarField::from(1)], 1);
        let expected = MultiPoly::from_coefficients_vec(
            1,
            vec![(ScalarField::from(1), SparseTerm::new(vec![(0, 1)]))],
        );
        assert_eq!(poly, expected);

        // Create a multivariate polynomial in 2 variable, with 1 term:
        // x_0*x_1
        let inputs = vec![3];
        let poly = multilinear_polynomial_from_evals(inputs, vec![ScalarField::from(1)], 2);
        let expected = MultiPoly::from_coefficients_vec(
            2,
            vec![(ScalarField::from(1), SparseTerm::new(vec![(0, 1), (1, 1)]))],
        );
        assert_eq!(poly, expected);

        // Create a multivariate polynomial in 2 variable, with 2 terms:
        // -x_0*x_1 + x_1
        let inputs = vec![1];
        let poly = multilinear_polynomial_from_evals(inputs, vec![ScalarField::from(1)], 2);
        let expected = MultiPoly::from_coefficients_vec(
            2,
            vec![
                (ScalarField::from(-1), SparseTerm::new(vec![(0, 1), (1, 1)])),
                (ScalarField::from(1), SparseTerm::new(vec![(1, 1)])),
            ],
        );
        assert_eq!(poly, expected);

        // Create a multivariate polynomial in 2 variable, with 2 terms:
        // -x_0*x_1 + x_0
        let inputs = vec![2];
        let poly = multilinear_polynomial_from_evals(inputs, vec![ScalarField::from(1)], 2);
        let expected = MultiPoly::from_coefficients_vec(
            2,
            vec![
                (ScalarField::from(-1), SparseTerm::new(vec![(0, 1), (1, 1)])),
                (ScalarField::from(1), SparseTerm::new(vec![(0, 1)])),
            ],
        );
        assert_eq!(poly, expected);

        // Create a multivariate polynomial in 4 variable, with 2 terms:
        // -x_0*x_1*x_2*x_3 + x_0*x_2
        let inputs = vec![11];
        let poly = multilinear_polynomial_from_evals(inputs, vec![ScalarField::from(1)], 4);
        let expected = MultiPoly::from_coefficients_vec(
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
        let inputs = vec![9];
        let poly = multilinear_polynomial_from_evals(inputs, vec![ScalarField::from(1)], 4);
        let expected = MultiPoly::from_coefficients_vec(
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
    }

    #[test]
    pub fn test_poly_binary() {
        // Create a multivariate polynomial in 1 variable, with 1 term:
        // 1 - x_0
        let inputs = "0";
        let poly = polynomial_from_binary(vec![inputs.chars()], vec![ScalarField::from(1)]);
        let expected = MultiPoly::from_coefficients_vec(
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
        let expected = MultiPoly::from_coefficients_vec(
            1,
            vec![(ScalarField::from(1), SparseTerm::new(vec![(0, 1)]))],
        );
        assert_eq!(poly, expected);

        // Create a multivariate polynomial in 2 variable, with 1 term:
        // x_0*x_1
        let inputs = "11";
        let poly = polynomial_from_binary(vec![inputs.chars()], vec![ScalarField::from(1)]);
        let expected = MultiPoly::from_coefficients_vec(
            2,
            vec![(ScalarField::from(1), SparseTerm::new(vec![(0, 1), (1, 1)]))],
        );
        assert_eq!(poly, expected);

        // Create a multivariate polynomial in 2 variable, with 2 terms:
        // -x_0*x_1 + x_1
        let inputs = "01";
        let poly = polynomial_from_binary(vec![inputs.chars()], vec![ScalarField::from(1)]);
        let expected = MultiPoly::from_coefficients_vec(
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
        let expected = MultiPoly::from_coefficients_vec(
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
        let expected = MultiPoly::from_coefficients_vec(
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
        let expected = MultiPoly::from_coefficients_vec(
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
        let expected = MultiPoly::from_coefficients_vec(
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
        let expected = MultiPoly::from_coefficients_vec(
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
    pub fn test_restrict_poly_to_line() {
        let poly = MultiPoly::from_coefficients_vec(
            2,
            vec![
                (ScalarField::from(3), SparseTerm::new(vec![(0, 1), (1, 1)])),
                (ScalarField::from(2), SparseTerm::new(vec![(1, 1)])),
            ],
        );

        let b = vec![ScalarField::from(2), ScalarField::from(4)];
        let c = vec![ScalarField::from(3), ScalarField::from(2)];

        let lines = unique_univariate_line(&b, &c);

        let restricted_poly = restrict_poly_to_line(poly, &lines);

        assert_eq!(
            restricted_poly,
            UniPoly::from_coefficients_slice(&[
                (0, ScalarField::from(32)),
                (1, ScalarField::from(-4)),
                (2, ScalarField::from(-6))
            ])
        )
    }
}
