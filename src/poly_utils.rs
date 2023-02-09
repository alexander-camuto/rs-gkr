use ark_bn254::Fr as ScalarField;
use ark_poly::polynomial::multivariate::{SparsePolynomial, SparseTerm, Term};
use ark_poly::DenseMVPolynomial;
use core::str::Chars;
use std::cmp::max;

pub type MultiPoly = SparsePolynomial<ScalarField, SparseTerm>;

pub fn mult_poly(p1: MultiPoly, p2: MultiPoly) -> MultiPoly {
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
    SparsePolynomial::from_coefficients_vec(num_vars, mult_terms)
}

pub fn shift_poly_by_k(p: MultiPoly, k: usize) -> MultiPoly {
    let terms = p.terms();
    let current_num_vars = p.num_vars();
    let mut shifted_terms = vec![];
    for (unit, term) in terms {
        let shifted_term = SparseTerm::new((*term).iter().map(|c| (c.0 + k, c.1)).collect());
        shifted_terms.push((*unit, shifted_term));
    }
    SparsePolynomial::from_coefficients_vec(current_num_vars + k, shifted_terms)
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
        DenseMVPolynomial,
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

        let poly2 = shift_poly_by_k(poly1, 3);

        assert_eq!(
            poly2,
            SparsePolynomial::from_coefficients_vec(
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
        let poly1 = SparsePolynomial::from_coefficients_vec(
            3,
            vec![
                (ScalarField::from(2), SparseTerm::new(vec![(0, 3)])),
                (ScalarField::from(2), SparseTerm::new(vec![(0, 1), (2, 1)])),
                (ScalarField::from(1), SparseTerm::new(vec![(1, 1), (2, 1)])),
                (ScalarField::from(5), SparseTerm::new(vec![])),
            ],
        );
        let poly2 = shift_poly_by_k(poly1, 3);
        assert_eq!(
            poly2,
            SparsePolynomial::from_coefficients_vec(
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
        let poly1 = SparsePolynomial::from_coefficients_vec(
            1,
            vec![
                (ScalarField::from(2), SparseTerm::new(vec![(0, 3)])),
                (ScalarField::from(5), SparseTerm::new(vec![])),
            ],
        );

        let poly2 = SparsePolynomial::from_coefficients_vec(
            4,
            vec![
                (ScalarField::from(2), SparseTerm::new(vec![(3, 3)])),
                (ScalarField::from(5), SparseTerm::new(vec![])),
            ],
        );

        let mult_poly = mult_poly(poly1, poly2);

        assert_eq!(mult_poly.num_vars(), 4);
        assert_eq!(
            mult_poly,
            SparsePolynomial::from_coefficients_vec(
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
}
