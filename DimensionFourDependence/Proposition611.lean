import DimensionFourDependence.Corollary610
import DimensionFourDependence.PlanarBlockNilpotence
import DimensionFourDependence.IndependentCovectorPairCoordinates

/-! # Proposition 6.11: ordinary tameness of the homogeneous quintic planar branch -/

namespace DimensionFourDependence

open Matrix MvPolynomial Module

set_option maxHeartbeats 1600000

variable {K : Type*} [Field K] [CharZero K]
local notation "R₄" => MvPolynomial (Fin 4) K
local notation "Aut₄" => R₄ ≃ₐ[K] R₄

theorem homogeneous_quintic_planar_is_tame
    (A : Fin 2 → R₄) (hA : ∀ i, (A i).IsHomogeneous 5)
    (hN : IsNilpotent (Shear.planarActiveJacobian A)) :
    ∃ E : Aut₄, E ∈ Tame.subgroup K 4 ∧
      ∀ j, E (X j) = X j + ![A 0, A 1, 0, 0] j := by
  obtain ⟨E, hE, _, _, h5⟩ := Shear.homogeneous_planar_nilpotent_tameness A hA hN
  exact ⟨E, h5 le_rfl Shear.corollary_6_10, hE⟩

/-- The span condition supplies two genuine constant relations.
The two fixed coordinates are moved to the final positions before
applying the planar theorem to the active block. -/
theorem homogeneous_quintic_span_at_most_two_is_tame
    (H : Fin 4 → R₄) (hH : IsHomogMap H 5) (hN : IsNilpotent (jac H))
    (hspan : finrank K (Submodule.span K (Set.range H)) ≤ 2) :
    ∃ E : Aut₄, E ∈ Tame.subgroup K 4 ∧ ∀ j, E (X j) = X j + H j := by
  obtain ⟨r, s, hli, hr, hs⟩ := component_span_at_most_two_constructs_independent_constant_relations H hspan
  obtain ⟨T, S, a, b, hTS, hST, hG⟩ :=
    two_independent_constant_relations_construct_two_axis_conjugacy H r s hli hr hs
  let G := linearPolynomialConjugate T S H
  let J : Matrix (Fin 4) (Fin 4) K := !![0, 0, 1, 0; 0, 0, 0, 1; 1, 0, 0, 0; 0, 1, 0, 0]
  have hJ : J * J = 1 := by
    funext i j
    fin_cases i <;> fin_cases j <;>
      simp [J, Matrix.mul_apply, Matrix.one_apply, Fin.sum_univ_succ]
  let W := linearPolynomialConjugate J J G
  have hW₂ : W 2 = 0 := by
    simp [W, G, hG, J, linearPolynomialConjugate, Fin.sum_univ_succ, linearPolynomialPullback]
  have hW₃ : W 3 = 0 := by
    simp [W, G, hG, J, linearPolynomialConjugate, Fin.sum_univ_succ, linearPolynomialPullback]
  let A : Fin 2 → R₄ := ![W 0, W 1]
  have hW : W = ![A 0, A 1, 0, 0] := by
    funext i
    fin_cases i
    · rfl
    · rfl
    · exact hW₂
    · exact hW₃
  have hGh := linearPolynomialConjugate_homogeneous T S H hH
  have hWh : IsHomogMap W 5 := linearPolynomialConjugate_homogeneous J J G hGh
  have hAh (i : Fin 2) : (A i).IsHomogeneous 5 := by
    fin_cases i
    · exact hWh 0
    · exact hWh 1
  have hGn := linearPolynomialConjugate_nilpotent T S hTS hST H hN
  have hWn : IsNilpotent (jac W) := linearPolynomialConjugate_nilpotent J J hJ hJ G hGn
  rw [hW] at hWn
  obtain ⟨F, hFt, hFX⟩ :=
    homogeneous_quintic_planar_is_tame A hAh (planarActiveJacobian_nilpotent_of_full_nilpotent A hWn)
  have hF (i : Fin 4) : F (X i) = X i + linearPolynomialConjugate J J G i := by
    change F (X i) = X i + W i
    rw [hW]
    exact hFX i
  obtain ⟨E, hEt, hEX⟩ := tame_automorphism_descends_from_constant_linear_conjugacy J J hJ hJ G F hF hFt
  exact tame_automorphism_descends_from_constant_linear_conjugacy T S hTS hST H E hEX hEt

end DimensionFourDependence
