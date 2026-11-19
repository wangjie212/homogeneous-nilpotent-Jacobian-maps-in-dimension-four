import DimensionFourDependence.PolynomialAutomorphismStabilization

/-! # Stabilizing ordinary tame words -/

namespace DimensionFourDependence.Tame

open MvPolynomial

variable {R : Type*} [CommRing R] {n : ℕ}
local notation "A" => MvPolynomial (Fin n) R

theorem stabilize_isAffine [Nontrivial R] (e : A ≃ₐ[R] A) (he : IsAffine e) :
    IsAffine (stabilize e) := by
  intro j
  refine Fin.lastCases ?_ (fun i => ?_) j
  · rw [stabilize_X_last, totalDegree_X]
  · rw [stabilize_X_castSucc]
    exact (totalDegree_rename_le _ _).trans (he i)

theorem stabilize_isElementary (e : A ≃ₐ[R] A) (he : IsElementary e) :
    IsElementary (stabilize e) := by
  obtain ⟨i, p, hp, hX⟩ := he
  refine ⟨i.castSucc, rename Fin.castSucc p, ?_, ?_⟩
  · intro h
    obtain ⟨k, hk, hki⟩ := mem_vars_rename Fin.castSucc p h
    exact hp ((Fin.castSucc_injective _ hki) ▸ hk)
  · intro j
    refine Fin.lastCases ?_ (fun k => ?_) j
    · rw [stabilize_X_last, if_neg (Fin.castSucc_ne_last i).symm, add_zero]
    · rw [stabilize_X_castSucc, hX, map_add, rename_X]
      by_cases h : k = i
      · subst k
        simp
      · rw [if_neg h, if_neg (fun he => h (Fin.castSucc_injective _ he)), map_zero]

/-- Each generator of the tame subgroup extends to a generator of the
larger tame subgroup under the actual fixed-variable extension. -/
theorem stabilize_mem_subgroup [Nontrivial R] (e : A ≃ₐ[R] A) (he : e ∈ subgroup R n) :
    stabilize e ∈ subgroup R (n + 1) := by
  have hle : subgroup R n ≤ (subgroup R (n + 1)).comap stabilize := by
    apply (Subgroup.closure_le _).mpr
    intro f hf
    apply Subgroup.subset_closure
    exact hf.imp (stabilize_isAffine f) (stabilize_isElementary f)
  exact hle he

end DimensionFourDependence.Tame
