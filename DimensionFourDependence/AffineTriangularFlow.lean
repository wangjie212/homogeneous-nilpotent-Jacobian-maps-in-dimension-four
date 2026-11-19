import DimensionFourDependence.AffineTangentNormalization
import DimensionFourDependence.CommutativePolynomialChainRule
import Mathlib.Algebra.Polynomial.Derivation

/-! # The polynomial flow of the actual affine triangular tangent field

The horizontal coefficients are constant and the vertical coefficient is
affine in the horizontal coordinates. Its flow is a polynomial of degree
two in an independent time variable. The chain rule identifies time
differentiation with the full original affine tangent action.
-/

namespace DimensionFourDependence

open MvPolynomial

set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 100000

variable {K : Type*} [Field K]

local notation "R" => MvPolynomial (Fin 3) K

/-- The entire polynomial flow, with all original x,z,w coordinates
retained as coefficients and a new independent time variable. -/
noncomputable def affineTriangularFlowPoint (u : Fin 2 → K) (b : Fin 3 → K) :
    Fin 3 → Polynomial R :=
  ![Polynomial.C (X 0) + Polynomial.C (C (u 0)) * Polynomial.X,
    Polynomial.C (X 1) + Polynomial.C (C (u 1)) * Polynomial.X,
    Polynomial.C (X 2) + Polynomial.C (affineTangentVerticalCoefficient b) * Polynomial.X +
      Polynomial.C (C ((b 1 * u 0 + b 2 * u 1) / 2)) * Polynomial.X ^ 2]

/-- Substitution along the actual full affine triangular polynomial flow. -/
noncomputable def affineTriangularFlow (u : Fin 2 → K) (b : Fin 3 → K) :
    R →ₐ[K] Polynomial R := aeval (affineTriangularFlowPoint u b)

/-- Every original variable is substituted by its explicit flow coordinate. -/
theorem affineTriangularFlow_X (u : Fin 2 → K) (b : Fin 3 → K) (i : Fin 3) :
    affineTriangularFlow u b (X i) = affineTriangularFlowPoint u b i := by
  exact aeval_X _ _

/-- Original scalar coefficients are constant in the independent flow time. -/
theorem affineTriangularFlow_C (u : Fin 2 → K) (b : Fin 3 → K) (a : K) :
    affineTriangularFlow u b (C a) = Polynomial.C (C a) := by
  exact (affineTriangularFlow u b).commutes a

/-- At time zero the whole actual polynomial flow is the original source. -/
theorem affineTriangularFlow_eval_zero (u : Fin 2 → K) (b : Fin 3 → K) (P : R) :
    Polynomial.eval 0 (affineTriangularFlow u b P) = P := by
  induction P using MvPolynomial.induction_on with
  | C a => rw [affineTriangularFlow_C, Polynomial.eval_C]
  | add P Q hP hQ => simp only [map_add, Polynomial.eval_add, hP, hQ]
  | mul_X P i hP =>
    rw [map_mul, Polynomial.eval_mul, hP, affineTriangularFlow_X]
    congr 1
    fin_cases i <;> simp [affineTriangularFlowPoint]

variable [CharZero K]

/-- Each flow coordinate has the actual triangular velocity evaluated
at that same flow point. -/
theorem affineTriangularFlowPoint_derivative
    (u : Fin 2 → K) (b : Fin 3 → K) (i : Fin 3) :
    (affineTriangularFlowPoint u b i).derivative =
      affineTriangularFlow u b
        ((![C (u 0), C (u 1), affineTangentVerticalCoefficient b] : Fin 3 → R) i) := by
  have hhalf : 2 * ((b 1 * u 0 + b 2 * u 1) / 2) = b 1 * u 0 + b 2 * u 1 := by
    field_simp
  fin_cases i
  · simp [affineTriangularFlowPoint]
  · simp [affineTriangularFlowPoint]
  · change (Polynomial.C (X 2) + Polynomial.C (affineTangentVerticalCoefficient b) * Polynomial.X +
        Polynomial.C (C ((b 1 * u 0 + b 2 * u 1) / 2)) * Polynomial.X ^ 2).derivative =
      affineTriangularFlow u b (affineTangentVerticalCoefficient b)
    simp only [Polynomial.derivative_mul, Polynomial.derivative_C,
      Polynomial.derivative_X, Polynomial.derivative_pow, zero_mul, zero_add, mul_one,
      affineTangentVerticalCoefficient, map_add, map_mul, affineTriangularFlow_C, affineTriangularFlow_X]
    simp only [affineTriangularFlowPoint, Matrix.cons_val_zero, Matrix.cons_val_one, map_natCast]
    have hmap := congrArg (fun a : K => (Polynomial.C (C a) : Polynomial R)) hhalf
    simp only [map_mul, map_add, map_ofNat] at hmap
    linear_combination Polynomial.X * hmap

/-- Time differentiation of every original polynomial agrees exactly
with its full affine triangular tangent action along the actual flow. -/
theorem affineTriangularFlow_derivative
    (u : Fin 2 → K) (b : Fin 3 → K) (P : R) :
    (affineTriangularFlow u b P).derivative =
      affineTriangularFlow u b (affineProjectedTangentAction u b P) := by
  have he := derivation_commutative_aeval_chain_rule
    ((show Derivation R (Polynomial R) (Polynomial R) from Polynomial.derivative').restrictScalars K)
      (affineTriangularFlowPoint u b) P
  change (affineTriangularFlow u b P).derivative =
    ∑ i : Fin 3, affineTriangularFlow u b (pderiv i P) *
      (affineTriangularFlowPoint u b i).derivative at he
  rw [he]
  simp only [affineTriangularFlowPoint_derivative, affineProjectedTangentAction, map_add, map_mul]
  simp [Fin.sum_univ_succ, mul_comm] <;> ring

/-- No nonzero polynomial eigenvector of an affine triangular tangent
field has a nonzero scalar eigenvalue. The constructed polynomial flow
reduces the claim to a univariate polynomial dividing its derivative. -/
theorem affine_triangular_polynomial_eigenvalue_zero
    (u : Fin 2 → K) (b : Fin 3 → K) (P : R) (hP : P ≠ 0) (a : K)
    (heigen : affineProjectedTangentAction u b P = C a * P) : a = 0 := by
  let Q := affineTriangularFlow u b P
  have hQ : Q ≠ 0 := by
    intro hz
    have h := congrArg (Polynomial.eval 0) hz
    rw [affineTriangularFlow_eval_zero, Polynomial.eval_zero] at h
    exact hP h
  have hd : Q.derivative = Polynomial.C (C a) * Q := by
    rw [affineTriangularFlow_derivative, heigen, map_mul, affineTriangularFlow_C]
  have hd0 : Q.derivative = 0 := Polynomial.dvd_derivative_iff.mp
    ⟨Polynomial.C (C a), by rw [hd, mul_comm]⟩
  have hc : Polynomial.C (C a : R) = 0 :=
    (mul_eq_zero.mp (hd.symm.trans hd0)).resolve_right hQ
  apply MvPolynomial.C_injective (Fin 3) K
  exact Polynomial.C_injective (hc.trans (by simp))

end DimensionFourDependence
