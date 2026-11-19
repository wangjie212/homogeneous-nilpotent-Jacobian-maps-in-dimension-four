import DimensionFourDependence.ParabolaFieldEmbedding
import Mathlib.RingTheory.Polynomial.IsIntegral
import Mathlib.RingTheory.Algebraic.Integral

/-! # Polynomial descent over algebraically closed constants

A polynomial over a field extension which is algebraic over the original
polynomial ring already has original-field coefficients. Clearing an
algebraic denominator gives an integral polynomial multiple; integrality
of coefficients and exact polynomial divisibility descend that multiple
and then the original polynomial. Monic divisors descend as well.
-/

namespace DimensionFourDependence

open Polynomial

attribute [local instance] Polynomial.algebra

set_option maxHeartbeats 1500000

variable {K F : Type*} [Field K] [IsAlgClosed K] [Field F] [Algebra K F]

/-- Integral coefficients over algebraically closed constants
construct the polynomial over the original coefficient field. -/
theorem integral_polynomial_coefficients_construct_base_polynomial
    (P : Polynomial F) (hP : ∀ i, IsIntegral K (P.coeff i)) :
    ∃ Q : Polynomial K, Q.map (algebraMap K F) = P := by
  classical
  have hex (i : ℕ) : ∃ a : K, algebraMap K F a = P.coeff i :=
    algebraic_value_preimage_of_isAlgClosed (P.coeff i) (hP i).isAlgebraic
  choose a ha using hex
  refine ⟨∑ i ∈ P.support, monomial i (a i), ?_⟩
  simp only [Polynomial.map_sum, Polynomial.map_monomial, ha]
  exact P.sum_monomial_eq

/-- A polynomial integral over the original polynomial ring has
its whole polynomial value in that ring. -/
theorem integral_polynomial_constructs_base_polynomial
    (P : Polynomial F) (hP : IsIntegral (Polynomial K) P) :
    ∃ Q : Polynomial K, Q.map (algebraMap K F) = P :=
  integral_polynomial_coefficients_construct_base_polynomial P (fun i => hP.coeff i)

/-- An algebraic polynomial over the original polynomial ring
actually descends to that ring. -/
theorem algebraic_polynomial_constructs_base_polynomial
    (P : Polynomial F) (hP : IsAlgebraic (Polynomial K) P) :
    ∃ Q : Polynomial K, Q.map (algebraMap K F) = P := by
  obtain ⟨r, hr, hint⟩ := hP.exists_integral_multiple
  obtain ⟨Q, hQ⟩ := integral_polynomial_constructs_base_polynomial (r • P) hint
  have hdiv : r.map (algebraMap K F) ∣ Q.map (algebraMap K F) := by
    refine ⟨P, ?_⟩
    exact hQ
  obtain ⟨q, hq⟩ := (Polynomial.map_dvd_map' (algebraMap K F)).mp hdiv
  refine ⟨q, ?_⟩
  apply mul_left_cancel₀ (Polynomial.map_ne_zero hr)
  calc
    r.map (algebraMap K F) * q.map (algebraMap K F) = Q.map (algebraMap K F) := by
      rw [hq, Polynomial.map_mul]
    _ = r.map (algebraMap K F) * P := hQ

/-- Every monic polynomial over an extension which divides an
original-field polynomial has original-field coefficients. -/
theorem monic_divisor_constructs_base_polynomial
    (P : Polynomial F) (hP : P.Monic) (Q : Polynomial K) (hQ : Q ≠ 0)
    (hdiv : P ∣ Q.map (algebraMap K F)) :
    ∃ P₀ : Polynomial K, P₀.map (algebraMap K F) = P := by
  let Q₀ := Q * C Q.leadingCoeff⁻¹
  have hQ₀ : Q₀.Monic := monic_mul_leadingCoeff_inv hQ
  have hdiv₀ : P ∣ Q₀.map (algebraMap K F) := by
    rw [Polynomial.map_mul]
    exact dvd_mul_of_dvd_left hdiv _
  exact integral_polynomial_coefficients_construct_base_polynomial P
    (Polynomial.isIntegral_coeff_of_dvd Q₀ P hQ₀ hP hdiv₀)

/-- A nonzero divisor of a nonzero original-field polynomial is
an original-field polynomial times its actual leading coefficient. -/
theorem polynomial_divisor_constructs_projective_base_polynomial
    (P : Polynomial F) (hP : P ≠ 0) (Q : Polynomial K) (hQ : Q ≠ 0)
    (hdiv : P ∣ Q.map (algebraMap K F)) :
    ∃ P₀ : Polynomial K, P = C P.leadingCoeff * P₀.map (algebraMap K F) := by
  let P₁ := P * C P.leadingCoeff⁻¹
  have hP₁ : P₁.Monic := monic_mul_leadingCoeff_inv hP
  have hP₁div : P₁ ∣ Q.map (algebraMap K F) := by
    apply dvd_trans ?_ hdiv
    refine ⟨C P.leadingCoeff, ?_⟩
    dsimp only [P₁]
    rw [mul_assoc, ← C_mul, inv_mul_cancel₀ (leadingCoeff_ne_zero.mpr hP), C_1, mul_one]
  obtain ⟨P₀, hP₀⟩ := monic_divisor_constructs_base_polynomial P₁ hP₁ Q hQ hP₁div
  refine ⟨P₀, ?_⟩
  rw [hP₀]
  dsimp only [P₁]
  rw [← mul_assoc, mul_comm (C P.leadingCoeff) P, mul_assoc,
    ← C_mul, mul_inv_cancel₀ (leadingCoeff_ne_zero.mpr hP), C_1, mul_one]

/-- A scalar-normalized power which is algebraic in the independent
parameter forces its polynomial root to descend projectively to the
original algebraically closed constants. -/
theorem algebraic_scaled_power_constructs_projective_polynomial_descent
    (P : Polynomial F) (hP : P ≠ 0) (h : F) (hh : h ≠ 0) (d : ℕ) (hd : 0 < d)
    (halg : IsAlgebraic (Polynomial K) (C h⁻¹ * P ^ d)) :
    ∃ P₀ : Polynomial K, P = C P.leadingCoeff * P₀.map (algebraMap K F) := by
  obtain ⟨Q, hQ⟩ := algebraic_polynomial_constructs_base_polynomial (C h⁻¹ * P ^ d) halg
  have hQ0 : Q ≠ 0 := by
    intro hz
    have he := hQ
    rw [hz, Polynomial.map_zero] at he
    exact (mul_ne_zero (C_ne_zero.mpr (inv_ne_zero hh)) (pow_ne_zero d hP)) he.symm
  have hdiv : P ∣ Q.map (algebraMap K F) := by
    rw [hQ]
    exact dvd_mul_of_dvd_right (dvd_pow_self P (Nat.ne_of_gt hd)) _
  exact polynomial_divisor_constructs_projective_base_polynomial P hP Q hQ0 hdiv

end DimensionFourDependence
