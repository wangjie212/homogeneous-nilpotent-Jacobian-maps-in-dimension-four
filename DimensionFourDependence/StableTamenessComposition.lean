import DimensionFourDependence.StabilizationPreservesTameness
import DimensionFourDependence.Proposition64

/-! # Ordinary tame automorphisms and products of one-stably tame automorphisms -/

namespace DimensionFourDependence.Shear

open MvPolynomial

variable {K : Type*} [Field K]
local notation "R₄" => MvPolynomial (Fin 4) K
local notation "Aut₄" => R₄ ≃ₐ[K] R₄

theorem oneStablyTame_of_tame (e : Aut₄) (he : e ∈ Tame.subgroup K 4) :
    IsOneStablyTame e :=
  ⟨Tame.stabilize e, Tame.stabilize_mem_subgroup e he,
    Tame.stabilize_X_last e, Tame.stabilize_comp_rename e⟩

/-- Extensions of two automorphisms compose with the same fixed coordinate. -/
theorem oneStablyTame_mul (e f : Aut₄) (he : IsOneStablyTame e) (hf : IsOneStablyTame f) :
    IsOneStablyTame (e * f) := by
  obtain ⟨E, hE, hEX, hEe⟩ := he
  obtain ⟨F, hF, hFX, hFf⟩ := hf
  refine ⟨E * F, (Tame.subgroup K 5).mul_mem hE hF, ?_, ?_⟩
  · rw [AlgEquiv.mul_apply, hFX, hEX]
  · change (E.toAlgHom.comp F.toAlgHom).comp (rename Fin.castSucc) =
      (rename Fin.castSucc).comp (e.toAlgHom.comp f.toAlgHom)
    rw [AlgHom.comp_assoc, hFf, ← AlgHom.comp_assoc, hEe, AlgHom.comp_assoc]

end DimensionFourDependence.Shear
