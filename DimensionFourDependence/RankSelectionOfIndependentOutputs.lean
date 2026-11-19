import DimensionFourDependence.RationalJacobianCriterion

/-! # Selecting actual independent output indices at any rational Jacobian rank -/

namespace DimensionFourDependence

open MvPolynomial Matrix

universe u

set_option maxHeartbeats 1600000

variable {K : Type u} [Field K] [CharZero K] {m n : ℕ}
local notation "F" => FractionRing (MvPolynomial (Fin n) K)

/-- The rational Jacobian rank selects that many actual output
components as a transcendence basis of the output field. -/
theorem jacobian_rank_selects_independent_output_indices
    (H : Fin m → F) {r : ℕ} (hrank : (rationalJacobian H).rank = r) :
    ∃ s : Fin r → Fin m, Function.Injective s ∧
      AlgebraicIndependent K (fun i => H (s i)) ∧
      ∀ j, IsAlgebraic (IntermediateField.adjoin K (Set.range (fun i => H (s i)))) (H j) := by
  classical
  obtain ⟨S, hS⟩ := (AlgebraicIndependent.matroid K F).exists_isBasis (Set.range H)
  rcases AlgebraicIndependent.matroid_isBasis_iff.mp hS with ⟨hSind, hsub, hAlg⟩
  have hfin : S.Finite := (Set.finite_range H).subset hsub
  let : Fintype S := hfin.fintype
  let chooseIndex : S → Fin m := fun a => Classical.choose (hsub a.property)
  have hindex (a : S) : H (chooseIndex a) = (a : F) := Classical.choose_spec (hsub a.property)
  have hinj : Function.Injective chooseIndex := by
    intro a b hab
    apply Subtype.ext
    rw [← hindex a, ← hindex b, hab]
  have hdata {k : ℕ} (e : Fin k ≃ S) :
      AlgebraicIndependent K (fun i => H (chooseIndex (e i))) ∧
      Set.range (fun i => H (chooseIndex (e i))) = S := by
    constructor
    · convert hSind.comp e e.injective using 1
      funext i
      exact hindex (e i)
    · ext a
      constructor
      · rintro ⟨i, rfl⟩
        change H (chooseIndex (e i)) ∈ S
        rw [hindex]
        exact (e i).property
      · intro h
        refine ⟨e.symm ⟨a, h⟩, ?_⟩
        change H (chooseIndex (e (e.symm ⟨a, h⟩))) = a
        rw [Equiv.apply_symm_apply, hindex]
  let e := (Fintype.equivFin S).symm
  obtain ⟨hind, hRange⟩ := hdata e
  have hAlgBasis (j : Fin m) :
      IsAlgebraic (IntermediateField.adjoin K (Set.range (fun i => H (chooseIndex (e i))))) (H j) := by
    rw [hRange]
    exact IntermediateField.isAlgebraic_adjoin_iff.mpr (hAlg _ ⟨j, rfl⟩)
  have htr := outputField_trdeg_of_independent_algebraic_generators _ hind H
    (by rw [hRange]; exact hsub) hAlgBasis
  have hcard : Fintype.card S = r := by
    have he := rationalJacobian_rank_eq_output_trdeg H
    rw [hrank, htr] at he
    exact_mod_cast he
  let er := (Fintype.equivFinOfCardEq hcard).symm
  obtain ⟨her, hRangeR⟩ := hdata er
  refine ⟨chooseIndex ∘ er, hinj.comp er.injective, her, ?_⟩
  intro j
  change IsAlgebraic (IntermediateField.adjoin K (Set.range (fun i => H (chooseIndex (er i))))) (H j)
  rw [hRangeR]
  exact IntermediateField.isAlgebraic_adjoin_iff.mpr (hAlg _ ⟨j, rfl⟩)

end DimensionFourDependence
