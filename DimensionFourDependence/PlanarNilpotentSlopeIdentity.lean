import DimensionFourDependence.RationalPartial

/-! # The mixed-partial identity for a planar nilpotent Jacobian slope -/

namespace DimensionFourDependence

set_option maxHeartbeats 2000000

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

/-- Trace and determinant give the three displayed first derivatives.
Equality of mixed partials then gives `s_x+s*s_y=0`. -/
theorem planar_slope_derivative_zero_of_mixed_partials
    (Dx Dy : Derivation K F F) (u v s : F) (hu : Dy u ≠ 0)
    (hux : Dx u = -(s * Dy u)) (hvy : Dy v = s * Dy u)
    (hvx : Dx v = -(s * s * Dy u))
    (hucomm : Dy (Dx u) = Dx (Dy u)) (hvcomm : Dy (Dx v) = Dx (Dy v)) :
    Dx s + s * Dy s = 0 := by
  have hx := congrArg Dy hux
  have hy := congrArg Dx hvy
  have hz := congrArg Dy hvx
  change Dy (Dx u) = Dy (-(s * Dy u)) at hx
  change Dx (Dy v) = Dx (s * Dy u) at hy
  change Dy (Dx v) = Dy (-(s * s * Dy u)) at hz
  simp only [map_neg, Derivation.leibniz, smul_eq_mul, hucomm] at hx
  simp only [Derivation.leibniz, smul_eq_mul] at hy
  simp only [map_neg, Derivation.leibniz, smul_eq_mul, hvcomm] at hz
  apply (mul_eq_zero.mp (show (Dx s + s * Dy s) * Dy u = 0 from ?_)).resolve_right hu
  linear_combination hz - hy - s * hx

open MvPolynomial

local notation "R₂" => MvPolynomial (Fin 2) K
local notation "F₂" => FractionRing R₂

/-- The derivation following the rational slope in the active plane. -/
noncomputable def planarSlopeDerivation (s : F₂) : Derivation K F₂ F₂ :=
  rationalPartial 0 + s • rationalPartial 1

theorem planarSlopeDerivation_first_coordinate (s : F₂) :
    planarSlopeDerivation s (rationalCoordinate 0) = 1 := by
  simp [planarSlopeDerivation, Derivation.add_apply, Derivation.smul_apply,
    rationalPartial_coordinate, smul_eq_mul]

theorem planarSlopeDerivation_second_coordinate (s : F₂) :
    planarSlopeDerivation s (rationalCoordinate 1) = s := by
  simp [planarSlopeDerivation, Derivation.add_apply, Derivation.smul_apply,
    rationalPartial_coordinate, smul_eq_mul]

/-- A nonzero vertical derivative supplies the rational slope and all
its required tangent identities in the actual source fraction field. -/
theorem planar_trace_determinant_construct_invariant_slope (u v : R₂)
    (hu : pderiv 1 u ≠ 0)
    (htr : pderiv 0 u + pderiv 1 v = 0)
    (hdet : pderiv 0 u * pderiv 1 v - pderiv 1 u * pderiv 0 v = 0) :
    ∃ s : F₂,
      planarSlopeDerivation s s = 0 ∧
      planarSlopeDerivation s (algebraMap R₂ F₂ u) = 0 ∧
      ∀ i : Fin 2, rationalPartial i (algebraMap R₂ F₂ v) =
        s * rationalPartial i (algebraMap R₂ F₂ u) := by
  let a := algebraMap R₂ F₂
  let s := a (pderiv 1 v) / a (pderiv 1 u)
  let Dx := rationalPartial (K := K) (0 : Fin 2)
  let Dy := rationalPartial (K := K) (1 : Fin 2)
  have ha : Function.Injective a := IsFractionRing.injective R₂ F₂
  have hau : a (pderiv 1 u) ≠ 0 := fun h => hu (ha (h.trans (map_zero a).symm))
  have hne : Dy (a u) ≠ 0 := by
    change rationalPartial 1 (a u) ≠ 0
    rw [rationalPartial_polynomial]
    exact hau
  have hvy : Dy (a v) = s * Dy (a u) := by
    change rationalPartial 1 (a v) = s * rationalPartial 1 (a u)
    rw [rationalPartial_polynomial, rationalPartial_polynomial]
    exact (div_mul_cancel₀ _ hau).symm
  have htr' : Dx (a u) + Dy (a v) = 0 := by
    change rationalPartial 0 (a u) + rationalPartial 1 (a v) = 0
    rw [rationalPartial_polynomial, rationalPartial_polynomial, ← map_add, htr, map_zero]
  have hux : Dx (a u) = -(s * Dy (a u)) := eq_neg_of_add_eq_zero_left (hvy ▸ htr')
  have hdet' : Dx (a u) * Dy (a v) - Dy (a u) * Dx (a v) = 0 := by
    change rationalPartial 0 (a u) * rationalPartial 1 (a v) -
      rationalPartial 1 (a u) * rationalPartial 0 (a v) = 0
    rw [rationalPartial_polynomial, rationalPartial_polynomial, rationalPartial_polynomial,
      rationalPartial_polynomial, ← map_mul, ← map_mul, ← map_sub, hdet, map_zero]
  have hvx : Dx (a v) = s * Dx (a u) := by
    rw [hvy] at hdet'
    apply (mul_left_cancel₀ hne)
    linear_combination -hdet'
  have hzero := planar_slope_derivative_zero_of_mixed_partials Dx Dy (a u) (a v) s hne hux hvy
    (by rw [hvx, hux]; ring) (rationalPartials_commute 1 0 _) (rationalPartials_commute 1 0 _)
  refine ⟨s, hzero, ?_, ?_⟩
  · change Dx (a u) + s * Dy (a u) = 0
    rw [hux, neg_add_cancel]
  · intro i
    fin_cases i
    · exact hvx
    · exact hvy

end DimensionFourDependence
