import DimensionFourDependence.BivariateRulingPowerFactorization

/-! # Exact coefficients and four-term normal form of the global bilinear factors -/

namespace DimensionFourDependence

open Polynomial

set_option maxHeartbeats 2500000

variable {K : Type*} [Field K]

/-- A degree-one bound retains precisely the actual constant and linear coefficients. -/
theorem polynomial_eq_constant_plus_linear_of_natDegree_le_one
    {R : Type*} [CommRing R] (P : Polynomial R) (hP : P.natDegree ≤ 1) :
    P = Polynomial.C (P.coeff 0) + Polynomial.C (P.coeff 1) * Polynomial.X := by
  ext n
  rcases n with _ | (_ | n)
  · simp
  · simp
  · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (hP.trans_lt (by omega : 1 < n + 2))]
    simp

/-- Exchanging the original two variables transposes the complete
coefficient array, with both outer and inner coefficients retained. -/
theorem bivariate_swap_coeff_coeff (P : Polynomial (Polynomial K)) (i j : ℕ) :
    ((Polynomial.Bivariate.swap P).coeff i).coeff j = (P.coeff j).coeff i := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ =>
    simp only [map_add, Polynomial.coeff_add, hP, hQ]
  | monomial m a =>
    induction a using Polynomial.induction_on' with
    | add a b ha hb =>
      simp only [map_add, Polynomial.coeff_add, ha, hb]
    | monomial n c =>
      rw [Polynomial.Bivariate.swap_monomial_monomial]
      by_cases hi : n = i <;> by_cases hj : m = j <;>
        simp [Polynomial.coeff_monomial, hi, hj, Ne.symm]

/-- The symmetric bidegree bound gives the individual original
coefficient-polynomial degree bounds, including every absent term. -/
theorem bivariate_bilinear_coeff_natDegree_le_one
    (P : Polynomial (Polynomial K)) (hP : BivariateBilinear P) (i : ℕ) :
    (P.coeff i).natDegree ≤ 1 := by
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro n hn
  rw [← bivariate_swap_coeff_coeff P n i]
  rw [Polynomial.coeff_eq_zero_of_natDegree_lt (hP.2.trans_lt hn)]
  simp

/-- A bilinear polynomial has precisely its four original constant
coefficients in the affine Segre chart. -/
theorem bivariate_bilinear_four_term_normal_form
    (P : Polynomial (Polynomial K)) (hP : BivariateBilinear P) :
    P = Polynomial.C (Polynomial.C ((P.coeff 0).coeff 0)) +
      Polynomial.C (Polynomial.C ((P.coeff 0).coeff 1) * Polynomial.X) +
      Polynomial.C (Polynomial.C ((P.coeff 1).coeff 0)) * Polynomial.X +
      Polynomial.C (Polynomial.C ((P.coeff 1).coeff 1) * Polynomial.X) * Polynomial.X := by
  have houter : P = Polynomial.C (P.coeff 0) + Polynomial.C (P.coeff 1) * Polynomial.X := by
    exact polynomial_eq_constant_plus_linear_of_natDegree_le_one P hP.1
  have hinner (i : ℕ) : P.coeff i = Polynomial.C ((P.coeff i).coeff 0) +
      Polynomial.C ((P.coeff i).coeff 1) * Polynomial.X :=
    polynomial_eq_constant_plus_linear_of_natDegree_le_one _ (bivariate_bilinear_coeff_natDegree_le_one P hP i)
  calc
    P = Polynomial.C (P.coeff 0) + Polynomial.C (P.coeff 1) * Polynomial.X := houter
    _ = _ := by
      conv_lhs => rw [hinner 0, hinner 1]
      simp only [Polynomial.C_add]
      ring

end DimensionFourDependence
