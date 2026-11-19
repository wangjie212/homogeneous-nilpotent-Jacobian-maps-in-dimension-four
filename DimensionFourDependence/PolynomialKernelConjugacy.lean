import DimensionFourDependence.LinearPolynomialConjugacy

/-! # The original polynomial right-kernel relation survives inverse source-target coordinates -/

namespace DimensionFourDependence

open MvPolynomial Matrix

set_option maxHeartbeats 2500000

variable {K : Type*} [Field K] {n : ℕ}

/-- The actual transformed polynomial kernel direction still lies in
the kernel of the actual transformed Jacobian. -/
theorem linearPolynomialConjugate_preserves_polynomial_right_kernel
    (T S : Matrix (Fin n) (Fin n) K) (hTS : T * S = 1)
    (H u : Fin n → MvPolynomial (Fin n) K) (hker : jac H *ᵥ u = 0) :
    jac (linearPolynomialConjugate T S H) *ᵥ linearPolynomialConjugate T S u = 0 := by
  let φ : MvPolynomial (Fin n) K →ₐ[K] MvPolynomial (Fin n) K := aeval (linearPolynomialMap T)
  have hmap : (jac H).map φ *ᵥ (fun i => φ (u i)) = 0 := by
    funext i
    have he := congrArg φ (congrFun hker i)
    simpa only [Matrix.mulVec, dotProduct, map_sum, map_mul, map_zero,
      Pi.zero_apply, Matrix.map_apply] using he
  have hTSmap : T.map (MvPolynomial.C : K →+* MvPolynomial (Fin n) K) * S.map MvPolynomial.C = 1 := by
    rw [← Matrix.map_mul, hTS]
    ext i j
    simp [Matrix.one_apply]
  rw [jac_linearPolynomialConjugate]
  change (S.map MvPolynomial.C * (jac H).map φ * T.map MvPolynomial.C) *ᵥ
    (S.map MvPolynomial.C *ᵥ fun i => φ (u i)) = 0
  rw [Matrix.mulVec_mulVec, Matrix.mul_assoc, hTSmap,
    Matrix.mul_one, ← Matrix.mulVec_mulVec, hmap, Matrix.mulVec_zero]

end DimensionFourDependence
