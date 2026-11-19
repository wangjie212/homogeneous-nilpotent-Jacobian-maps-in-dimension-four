import DimensionFourDependence.OutputSelection

/-! # The Jacobian rank of an independent rectangular output family

Extend independent outputs to a finite transcendence basis chosen among
them and the rational source coordinates. Its size is the source dimension.
The checked square Jacobian criterion then gives independent rows, and
restriction gives the rectangular assertion.
-/

namespace DimensionFourDependence

open MvPolynomial Matrix

variable {K : Type*} [Field K] {n m : ℕ}

/-- The actual rational source coordinates are algebraically independent. -/
theorem rationalCoordinates_algebraicIndependent :
    AlgebraicIndependent K (rationalCoordinate (K := K) (n := n)) := by
  exact (MvPolynomial.algebraicIndependent_X (Fin n) K).map'
    (f := IsScalarTower.toAlgHom K (MvPolynomial (Fin n) K) (FractionRing (MvPolynomial (Fin n) K)))
    (IsFractionRing.injective _ _)

/-- The source rational function field has its actual coordinate transcendence degree. -/
theorem rationalSource_trdeg_eq : Algebra.trdeg K (FractionRing (MvPolynomial (Fin n) K)) = n := by
  apply le_antisymm rationalSource_trdeg_le
  simpa using
    (rationalCoordinates_algebraicIndependent (K := K) (n := n)).lift_cardinalMk_le_trdeg

variable [CharZero K]

/-- An independent rectangular rational output family has independent
Jacobian rows, with the completion to a square family constructed. -/
theorem rationalJacobian_rows_independent
    (Y : Fin m → FractionRing (MvPolynomial (Fin n) K)) (hY : AlgebraicIndependent K Y) :
    LinearIndependent (FractionRing (MvPolynomial (Fin n) K)) (rationalJacobian Y).row := by
  classical
  let F := FractionRing (MvPolynomial (Fin n) K)
  let T : Set F := Set.range Y ∪ Set.range (rationalCoordinate (K := K) (n := n))
  let : Algebra.IsAlgebraic (Algebra.adjoin K T) F :=
    rationalSource_isAlgebraic_adjoin_of_coords_subset (by exact Set.subset_union_right)
  obtain ⟨S, hYS, hST, hS⟩ := exists_isTranscendenceBasis_between (R := K) (Set.range Y) T
    Set.subset_union_left hY.coe_range
  have hfin : S.Finite := ((Set.finite_range Y).union (Set.finite_range (rationalCoordinate (K := K) (n := n)))).subset hST
  let : Fintype S := hfin.fintype
  have hc : Fintype.card S = n := by
    have he := hS.cardinalMk_eq_trdeg
    rw [rationalSource_trdeg_eq, Cardinal.mk_fintype] at he
    exact_mod_cast he
  let e : Fin n ≃ S := (Fintype.equivFinOfCardEq hc).symm
  let Z : Fin n → F := fun i => (e i : F)
  have hZ : AlgebraicIndependent K Z := hS.1.comp e e.injective
  have hrZ := rationalJacobian_rank_of_square_independent Z hZ
  have hrows : LinearIndependent F (rationalJacobian Z).row := by
    apply linearIndependent_iff_card_eq_finrank_span.mpr
    rw [Set.finrank, ← Matrix.rank_eq_finrank_span_row, hrZ]
    simp only [Fintype.card_fin]
  let f : Fin m → Fin n := fun i => e.symm ⟨Y i, hYS ⟨i, rfl⟩⟩
  have hf (i : Fin m) : Z (f i) = Y i := by
    change (e (e.symm ⟨Y i, hYS ⟨i, rfl⟩⟩) : F) = Y i
    rw [e.apply_symm_apply]
  have hfi : Function.Injective f := by
    intro i j hij
    apply hY.injective
    rw [← hf i, ← hf j, hij]
  have he : (rationalJacobian Y).row = (rationalJacobian Z).row ∘ f := by
    funext i j
    change rationalPartial (K := K) j (Y i) = rationalPartial (K := K) j (Z (f i))
    rw [hf]
  rw [he]
  exact hrows.comp f hfi

/-- The rectangular Jacobian criterion for algebraically independent rational functions. -/
theorem rationalJacobian_rank_of_independent
    (Y : Fin m → FractionRing (MvPolynomial (Fin n) K)) (hY : AlgebraicIndependent K Y) :
    (rationalJacobian Y).rank = m := by
  simpa only [Fintype.card_fin] using (rationalJacobian_rows_independent Y hY).rank_matrix

end DimensionFourDependence
