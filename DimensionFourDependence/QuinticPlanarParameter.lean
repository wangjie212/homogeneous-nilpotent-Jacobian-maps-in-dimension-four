import DimensionFourDependence.Proposition63

/-! # The residual quintic shear has a constant multiplier -/

namespace DimensionFourDependence.Shear

open MvPolynomial

variable {K : Type*} [Field K]
local notation "R₂" => MvPolynomial (Fin 2) K
local notation "R₃" => MvPolynomial (Fin 3) K

/-- With quadratic coefficients in degree five, (6.9) leaves precisely
a scalar multiple of the invariant variable. -/
theorem quintic_quadratic_shear_parameter_linear
    (f : Polynomial R₂) (hzero : f.coeff 0 = 0)
    (hw : ∀ j, f.coeff j ≠ 0 → j * (2 + 1) ≤ 5 - 2 ∧
      (f.coeff j).IsHomogeneous (5 - 2 - j * (2 + 1))) :
    ∃ c : K, f = Polynomial.C (C c) * Polynomial.X := by
  let c := (f.coeff 1).coeff 0
  have hc : f.coeff 1 = C c := by
    by_cases hz : f.coeff 1 = 0
    · simp [c, hz, MvPolynomial.coeff_zero]
    · exact totalDegree_eq_zero_iff_eq_C.mp ((hw 1 hz).2.totalDegree hz)
  refine ⟨c, Polynomial.ext fun j => ?_⟩
  rw [Polynomial.coeff_C_mul_X]
  by_cases hj : j = 1
  · simpa [hj] using hc
  · rw [if_neg hj]
    rcases Nat.eq_zero_or_pos j with rfl | hp
    · exact hzero
    · by_contra! hz
      have hb := (hw j hz).1
      omega

/-- The scalar multiplier uses the same parameter polynomial as the
normalized shear automorphism. -/
theorem planarInvariantParameter3_scalar_linear (c : K) :
    planarInvariantParameter3 (Polynomial.C (C c) * Polynomial.X) = (C c * X 0 : R₃) := by
  simp [planarInvariantParameter3, Polynomial.eval₂_mul]

end DimensionFourDependence.Shear
