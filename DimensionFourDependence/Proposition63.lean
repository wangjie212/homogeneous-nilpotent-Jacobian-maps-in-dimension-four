import DimensionFourDependence.PlanarNonzeroShearNormalForm
import DimensionFourDependence.PlanarElementaryNormalForm
import DimensionFourDependence.PlanarTargetTranslation

/-! # Proposition 6.3 in the original polynomial algebra -/

namespace DimensionFourDependence.Shear

open MvPolynomial

variable {K : Type*} [Field K] [CharZero K]
local notation "R₂" => MvPolynomial (Fin 2) K
local notation "R₄" => MvPolynomial (Fin 4) K
local notation "Aut₄" => R₄ ≃ₐ[K] R₄

/-- After the two elementary target translations, the given planar
perturbation is elementary or has precisely the form (6.8)–(6.9). -/
theorem proposition_6_3
    (A : Fin 2 → R₄) {d : ℕ} (hA : ∀ i, (A i).IsHomogeneous d)
    (hN : IsNilpotent (planarActiveJacobian A)) :
    ∃ T F : Aut₄,
      T ∈ Tame.subgroup K 4 ∧
      (∀ j, T (X j) = X j + ![base4 (planarActiveConstant (A 0)),
        base4 (planarActiveConstant (A 1)), 0, 0] j) ∧
      (∀ j, F (X j) = X j + ![planarActiveNormalized (A 0), planarActiveNormalized (A 1), 0, 0] j) ∧
      (∀ j, (F * T) (X j) = X j + ![A 0, A 1, 0, 0] j) ∧
      (Tame.IsElementary F ∨ ∃ (r : ℕ) (a b : R₂) (f : Polynomial R₂),
        a ≠ 0 ∧ b ≠ 0 ∧ IsRelPrime a b ∧ a.IsHomogeneous r ∧ b.IsHomogeneous r ∧
        2 * r + 1 ≤ d ∧ f.coeff 0 = 0 ∧ f ≠ 0 ∧
        (∀ j, f.coeff j ≠ 0 →
          j * (r + 1) ≤ d - r ∧ (f.coeff j).IsHomogeneous (d - r - j * (r + 1))) ∧
        F = automorphism4 a b (planarInvariantParameter3 f)) := by
  classical
  obtain ⟨T, hT, hTX⟩ := planar_target_translation A
  by_cases h : planarActiveNormalized (A 0) = 0 ∨ planarActiveNormalized (A 1) = 0
  · obtain ⟨i, p, hp, hF⟩ := normalized_planar_zero_component_is_elementary A hN h
    let F : Aut₄ := Tame.elementary i p hp
    exact ⟨T, F, hT, hTX, hF, planar_target_translation_restores_original A F T hF hTX,
      Or.inl ⟨i, p, hp, Tame.elementary_X i p hp⟩⟩
  · obtain ⟨r, a, b, f, ha, hb, hc, had, hbd, hd, hf0, hf, hw, he⟩ :=
      normalized_planar_nonzero_pair_constructs_shear A hA hN
        (fun h0 => h (Or.inl h0)) (fun h1 => h (Or.inr h1))
    let F : Aut₄ := automorphism4 a b (planarInvariantParameter3 f)
    have hF (j : Fin 4) : F (X j) =
        X j + ![planarActiveNormalized (A 0), planarActiveNormalized (A 1), 0, 0] j := by
      rw [he]
      exact automorphism4_X _ _ _ j
    exact ⟨T, F, hT, hTX, hF, planar_target_translation_restores_original A F T hF hTX,
      Or.inr ⟨r, a, b, f, ha, hb, hc, had, hbd, hd, hf0, hf, hw, rfl⟩⟩

end DimensionFourDependence.Shear
