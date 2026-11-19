import DimensionFourDependence.ConstantCoefficientShearTameness
import DimensionFourDependence.LinearCoefficientShearTameness

/-! # The ordinary tameness assertion of Proposition 6.4 -/

namespace DimensionFourDependence.Shear

open MvPolynomial

variable {K : Type*} [Field K] [CharZero K]

/-- **Proposition 6.4, low-degree assertion.** If two coprime
coefficient forms are homogeneous of the same degree at most one,
their shear is tame in the original four variables. -/
theorem proposition_6_4_low_degree (a b : MvPolynomial (Fin 2) K)
    (f : MvPolynomial (Fin 3) K) {r : ℕ} (hr : r ≤ 1)
    (ha : a.IsHomogeneous r) (hb : b.IsHomogeneous r) (hc : IsRelPrime a b) :
    automorphism4 a b f ∈ Tame.subgroup K 4 := by
  rcases (show r = 0 ∨ r = 1 by omega) with rfl | rfl
  · rw [eq_C_of_isHomogeneous_zero ha, eq_C_of_isHomogeneous_zero hb]
    exact automorphism4_constant_coefficients_tame _ _ f
  · exact automorphism4_coprime_linear_coefficients_tame a b ha hb hc f

/-- All conclusions of Proposition 6.4 on the low-degree family,
for the same actual automorphism and the same polynomial coordinates. -/
theorem proposition_6_4 (a b : MvPolynomial (Fin 2) K)
    (f : MvPolynomial (Fin 3) K) :
    (∀ j, automorphism4 a b f (X j) = X j + perturbation4 a b f j) ∧
    (automorphism4 a b f).symm = automorphism4 a b (-f) ∧
    jac (perturbation4 a b f) ^ 3 = 0 ∧ IsOneStablyTame (automorphism4 a b f) ∧
    (∀ r ≤ 1, a.IsHomogeneous r → b.IsHomogeneous r → IsRelPrime a b →
      automorphism4 a b f ∈ Tame.subgroup K 4) := by
  obtain ⟨hX, hinv, hjac, hstable⟩ := proposition_6_4_general a b f
  exact ⟨hX, hinv, hjac, hstable, fun _ hr ha hb hc =>
    proposition_6_4_low_degree a b f hr ha hb hc⟩

end DimensionFourDependence.Shear
