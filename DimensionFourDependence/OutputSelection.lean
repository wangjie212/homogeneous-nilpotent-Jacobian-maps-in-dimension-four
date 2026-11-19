import DimensionFourDependence.JacobianRank

/-! # Selecting the independent output triple from rank three

This supplies the output-field reduction at the start of Lemma 2.2.
The simultaneous change of source and output coordinates is separate.
-/

namespace DimensionFourDependence

open Matrix

variable {K : Type*} [Field K] [CharZero K]

/-- A rank-three rational map in four variables has three independent
components, and every component is algebraic over their generated field. -/
theorem exists_independent_output_triple
    (H : Fin 4 → FractionRing (MvPolynomial (Fin 4) K))
    (hrank : (rationalJacobian H).rank = 3) :
    ∃ s : Fin 3 → Fin 4, Function.Injective s ∧
      AlgebraicIndependent K (fun i => H (s i)) ∧
      ∀ j, IsAlgebraic (IntermediateField.adjoin K (Set.range (fun i => H (s i)))) (H j) := by
  classical
  obtain ⟨S, hS⟩ := (AlgebraicIndependent.matroid K
    (FractionRing (MvPolynomial (Fin 4) K))).exists_isBasis (Set.range H)
  rcases AlgebraicIndependent.matroid_isBasis_iff.mp hS with ⟨hSind, hsub, hAlg⟩
  have hfin : S.Finite := (Set.finite_range H).subset hsub
  let : Fintype S := hfin.fintype
  change AlgebraicIndependent K (fun a : S => (a : FractionRing (MvPolynomial (Fin 4) K))) at hSind
  let f : S → Fin 4 := fun a => Classical.choose (hsub a.property)
  have hf (a : S) : H (f a) = (a : FractionRing (MvPolynomial (Fin 4) K)) :=
    Classical.choose_spec (hsub a.property)
  have hfi : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    rw [← hf a, ← hf b, hab]
  have hcard : Fintype.card S ≤ 4 := by
    simpa using Fintype.card_le_of_injective f hfi
  have hind {d : ℕ} (e : Fin d ≃ S) :
      AlgebraicIndependent K (fun i => H (f (e i))) := by
    convert hSind.comp e e.injective using 1
    funext i
    exact hf (e i)
  have hrange {d : ℕ} (e : Fin d ≃ S) : Set.range (fun i => H (f (e i))) = S := by
    ext z
    constructor
    · rintro ⟨i, rfl⟩
      change H (f (e i)) ∈ S
      rw [hf]
      exact (e i).property
    · intro hz
      refine ⟨e.symm ⟨z, hz⟩, ?_⟩
      change H (f (e (e.symm ⟨z, hz⟩))) = z
      rw [e.apply_symm_apply, hf]
  let e := (Fintype.equivFin S).symm
  have hAlgY : ∀ j, IsAlgebraic
      (IntermediateField.adjoin K (Set.range (fun i => H (f (e i))))) (H j) := by
    intro j
    rw [hrange e]
    exact IntermediateField.isAlgebraic_adjoin_iff.mpr (hAlg _ ⟨j, rfl⟩)
  have hlow : 3 ≤ Fintype.card S := by
    have hb := rationalJacobian_rank_le_of_algebraic_outputs _ (hind e) H hAlgY
    omega
  have hne : Fintype.card S ≠ 4 := by
    intro hc
    let e4 := (Fintype.equivFinOfCardEq hc).symm
    have hfull := rationalJacobian_rank_of_square_independent _ (hind e4)
    have hj : rationalJacobian (fun i => H (f (e4 i))) =
        (rationalJacobian H).submatrix (fun i => f (e4 i)) id := rfl
    have hle := Matrix.rank_submatrix_le (rationalJacobian H) (fun i => f (e4 i)) id
    rw [← hj, hfull, hrank] at hle
    omega
  have hc : Fintype.card S = 3 := by omega
  let e3 := (Fintype.equivFinOfCardEq hc).symm
  refine ⟨fun i => f (e3 i), hfi.comp e3.injective, hind e3, ?_⟩
  intro j
  rw [hrange e3]
  exact IntermediateField.isAlgebraic_adjoin_iff.mpr (hAlg _ ⟨j, rfl⟩)

end DimensionFourDependence
