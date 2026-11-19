import DimensionFourDependence.LinearPowerCoefficientDescent
import DimensionFourDependence.LinearPowerQuotientRecovery
import DimensionFourDependence.PrimitiveBoundaryImage

/-! # The binary Hessian isolates the repeated linear factor on an original ruling -/

namespace DimensionFourDependence

open MvPolynomial

set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 100000

variable {K E : Type*} [Field K] [Field E]

/-- The actual determinant of the two original second partials of a binary form. -/
noncomputable def binaryHessianDeterminant (P : MvPolynomial (Fin 2) K) :
    MvPolynomial (Fin 2) K :=
  pderiv 0 (pderiv 0 P) * pderiv 1 (pderiv 1 P) -
    pderiv 0 (pderiv 1 P) * pderiv 1 (pderiv 0 P)

/-- The actual second derivative of a linear form times a power of
another linear form retains both original coefficient covectors. -/
theorem binary_linear_power_second_partial
    (a b : Fin 2 → K) (d : ℕ) (i j : Fin 2) :
    pderiv i (pderiv j (linearFormPolynomial a * linearFormPolynomial b ^ d)) =
      (d : MvPolynomial (Fin 2) K) * (C (a i) * C (b j) + C (a j) * C (b i)) *
        linearFormPolynomial b ^ (d - 1) +
      (d : MvPolynomial (Fin 2) K) * ((d - 1 : ℕ) : MvPolynomial (Fin 2) K) *
        linearFormPolynomial a * C (b i) * C (b j) * linearFormPolynomial b ^ (d - 2) := by
  simp [pderiv_mul, pderiv_pow, linearFormPolynomial_pderiv, Nat.sub_sub]
  ring

/-- The exact binary Hessian determinant is a nonzero scalar times
only the repeated factor whenever the two original linear forms are independent. -/
theorem binary_linear_power_hessian_identity
    (a b : Fin 2 → K) (d : ℕ) :
    binaryHessianDeterminant (linearFormPolynomial a * linearFormPolynomial b ^ d) =
      C (-((d : K) ^ 2) * (a 0 * b 1 - a 1 * b 0) ^ 2) *
        linearFormPolynomial b ^ (2 * d - 2) := by
  unfold binaryHessianDeterminant
  rw [binary_linear_power_second_partial, binary_linear_power_second_partial,
    binary_linear_power_second_partial, binary_linear_power_second_partial]
  have he : 2 * d - 2 = (d - 1) * 2 := by omega
  rw [he, pow_mul]
  simp only [map_mul, map_neg, map_pow, map_sub, map_natCast]
  ring

/-- The original coefficient embedding preserves the entire original
binary Hessian determinant, with the same two coordinate labels. -/
theorem binaryHessianDeterminant_map (f : K →+* E) (P : MvPolynomial (Fin 2) K) :
    MvPolynomial.map f (binaryHessianDeterminant P) =
      binaryHessianDeterminant (MvPolynomial.map f P) := by
  simp only [binaryHessianDeterminant, map_sub, map_mul, pderiv_map]

end DimensionFourDependence
