import DimensionFourDependence.QuinticPlanarParameter
import DimensionFourDependence.Proposition64LowDegree
import DimensionFourDependence.StableTamenessComposition

/-! # Stable tameness of the dependent planar family and the degree-five reduction -/

namespace DimensionFourDependence.Shear

open MvPolynomial

variable {K : Type*} [Field K] [CharZero K]
local notation "R₂" => MvPolynomial (Fin 2) K
local notation "R₄" => MvPolynomial (Fin 4) K
local notation "Aut₄" => R₄ ≃ₐ[K] R₄

/-- The remaining constant-multiplier assertion for a binary quadratic pencil. -/
def QuadraticPencilShearsTame (K : Type*) [Field K] : Prop :=
  ∀ (a b : MvPolynomial (Fin 2) K), IsRelPrime a b →
    a.IsHomogeneous 2 → b.IsHomogeneous 2 → ∀ c : K,
    automorphism4 a b (C c * X 0) ∈ Tame.subgroup K 4

/-- The actual original planar map is one-stably tame in arbitrary
degree and tame through degree four. In degree five, ordinary tameness
reduces to Corollary 6.10. -/
theorem homogeneous_planar_nilpotent_tameness
    (A : Fin 2 → R₄) {d : ℕ} (hA : ∀ i, (A i).IsHomogeneous d)
    (hN : IsNilpotent (planarActiveJacobian A)) :
    ∃ E : Aut₄, (∀ j, E (X j) = X j + ![A 0, A 1, 0, 0] j) ∧
      IsOneStablyTame E ∧ (d ≤ 4 → E ∈ Tame.subgroup K 4) ∧
      (d ≤ 5 → QuadraticPencilShearsTame K → E ∈ Tame.subgroup K 4) := by
  obtain ⟨T, F, hT, _, _, hE, hF⟩ := proposition_6_3 A hA hN
  have hstableT := oneStablyTame_of_tame T hT
  refine ⟨F * T, hE, ?_, ?_, ?_⟩
  · apply oneStablyTame_mul _ _ _ hstableT
    rcases hF with h | ⟨r, a, b, f, ha, hb, hc, had, hbd, hd, hf0, hf, hw, rfl⟩
    · exact oneStablyTame_of_tame _ (Subgroup.subset_closure (Or.inr h))
    · exact automorphism4_oneStablyTame _ _ _
  · intro hd4
    apply (Tame.subgroup K 4).mul_mem _ hT
    rcases hF with h | ⟨r, a, b, f, ha, hb, hc, had, hbd, hd, hf0, hf, hw, rfl⟩
    · exact Subgroup.subset_closure (Or.inr h)
    · exact proposition_6_4_low_degree _ _ _ (by omega) had hbd hc
  · intro hd5 hquadratic
    apply (Tame.subgroup K 4).mul_mem _ hT
    rcases hF with h | ⟨r, a, b, f, ha, hb, hc, had, hbd, hd, hf0, hf, hw, rfl⟩
    · exact Subgroup.subset_closure (Or.inr h)
    · by_cases hr : r ≤ 1
      · exact proposition_6_4_low_degree _ _ _ hr had hbd hc
      · have hr2 : r = 2 := by omega
        have hd' : d = 5 := by omega
        subst r
        subst d
        obtain ⟨c, rfl⟩ := quintic_quadratic_shear_parameter_linear f hf0 hw
        rw [planarInvariantParameter3_scalar_linear]
        exact hquadratic a b hc had hbd c

end DimensionFourDependence.Shear
