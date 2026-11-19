import DimensionFourDependence.FixedCoordinateTamenessReduction
import DimensionFourDependence.StableTameConjugacy

/-! # Restoring the Section 6.2 translations with a fixed auxiliary variable -/

namespace DimensionFourDependence

open MvPolynomial Matrix

variable {K : Type*} [Field K]
local notation "R₄" => MvPolynomial (Fin 4) K
local notation "Aut₄" => R₄ ≃ₐ[K] R₄

/-- Restoring the fixed-coordinate translation and constant frame preserves
the checked one-stable extension, and preserves ordinary tameness when
the homogeneous core is already tame. -/
theorem normalized_fixed_coordinate_core_stable_tameness_restores_original_map
    (H : Fin 4 → R₄)
    (T S : Matrix (Fin 4) (Fin 4) K) (hTS : T * S = 1) (hST : S * T = 1)
    (B : Fin 3 → R₄) {d : ℕ}
    (hG : linearPolynomialConjugate T S H = Fin.lastCases 0 B)
    (hB : ∀ i, (B i).IsHomogeneous d)
    (e : Aut₄) (he : ∀ j, e (X j) = X j + normalizedFixedCoordinateHomogeneousCore B d j)
    (hes : Shear.IsOneStablyTame e) :
    ∃ E : Aut₄, (∀ j, E (X j) = X j + H j) ∧ Shear.IsOneStablyTame E ∧
      (e ∈ Tame.subgroup K 4 → E ∈ Tame.subgroup K 4) := by
  let τ := fixedCoordinateTranslation4 (fixedCoordinateChartConstants B) d
  have hτ := fixedCoordinateTranslation4_tame (fixedCoordinateChartConstants B) d
  have heq := automorphism_eq_perturbedPolynomialSubstitution _ e he
  have hcoords (j : Fin 4) :
      (e * τ) (X j) = X j + linearPolynomialConjugate T S H j := by
    have hf := AlgHom.congr_fun (fixed_coordinate_chart_target_translation_factorization B hB) (X j)
    have hes' := AlgHom.congr_fun heq (τ (X j))
    change e (τ (X j)) = aeval
      (fun j : Fin 4 => X j + normalizedFixedCoordinateHomogeneousCore B d j) (τ (X j)) at hes'
    change e (τ (X j)) = _
    rw [hes', hG]
    simpa only [aeval_X, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom,
      normalizedFixedCoordinateHomogeneousCore] using hf.symm
  obtain ⟨E, hX, hstable, htransfer⟩ :=
    one_stably_tame_automorphism_descends_from_constant_linear_conjugacy T S hTS hST H
      (e * τ) hcoords (Shear.oneStablyTame_mul _ _ hes (Shear.oneStablyTame_of_tame τ hτ))
  exact ⟨E, hX, hstable, fun hc => htransfer ((Tame.subgroup K 4).mul_mem hc hτ)⟩

end DimensionFourDependence
