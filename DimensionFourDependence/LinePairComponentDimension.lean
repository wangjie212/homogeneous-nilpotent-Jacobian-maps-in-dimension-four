import DimensionFourDependence.LinePairComponentGeometry
import DimensionFourDependence.GeneratedAlgebraDimension

/-! # The actual product of two covering curves has dimension at most two

The original component quotient rings embed in the actual pair-coordinate
quotient. Their images generate that quotient. The joint-generator
dimension bound therefore bounds its transcendence degree by two when
both original parameter function fields have dimension one.
-/

namespace DimensionFourDependence

open MvPolynomial Matrix

variable {K : Type*} [Field K] [IsAlgClosed K]
variable (Q Q' : Ideal (MvPolynomial LineMatrixIndex K)) [Q.IsPrime] [Q'.IsPrime]

local notation "PairRing" => (MvPolynomial LinePairIndex K ⧸ lineComponentPairIdeal Q Q')
local notation "LeftRing" => (MvPolynomial LineMatrixIndex K ⧸ Q)
local notation "RightRing" => (MvPolynomial LineMatrixIndex K ⧸ Q')

/-- The original left component quotient inside the actual pair-coordinate quotient. -/
noncomputable def linePairLeftCoordinateHom : LeftRing →ₐ[K] PairRing :=
  Ideal.quotientMapₐ (lineComponentPairIdeal Q Q') (MvPolynomial.rename Sum.inl)
    (by rw [lineComponentPairIdeal_comap_left Q Q'])

/-- The original right component quotient inside the actual pair-coordinate quotient. -/
noncomputable def linePairRightCoordinateHom : RightRing →ₐ[K] PairRing :=
  Ideal.quotientMapₐ (lineComponentPairIdeal Q Q') (MvPolynomial.rename Sum.inr)
    (by rw [lineComponentPairIdeal_comap_right Q Q'])

/-- The left coordinate map is the actual renaming on polynomial representatives. -/
theorem linePairLeftCoordinateHom_mk (P : MvPolynomial LineMatrixIndex K) :
    linePairLeftCoordinateHom Q Q' (Ideal.Quotient.mk Q P) =
      Ideal.Quotient.mk (lineComponentPairIdeal Q Q') (rename Sum.inl P) := rfl

/-- The right coordinate map is the actual renaming on polynomial representatives. -/
theorem linePairRightCoordinateHom_mk (P : MvPolynomial LineMatrixIndex K) :
    linePairRightCoordinateHom Q Q' (Ideal.Quotient.mk Q' P) =
      Ideal.Quotient.mk (lineComponentPairIdeal Q Q') (rename Sum.inr P) := rfl

/-- No original left component relation is lost in the actual pair quotient. -/
theorem linePairLeftCoordinateHom_injective : Function.Injective (linePairLeftCoordinateHom Q Q') := by
  apply (injective_iff_map_eq_zero _).mpr
  intro a ha
  obtain ⟨P, rfl⟩ := Ideal.Quotient.mk_surjective a
  rw [linePairLeftCoordinateHom_mk, Ideal.Quotient.eq_zero_iff_mem] at ha
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  change P ∈ (lineComponentPairIdeal Q Q').comap (MvPolynomial.rename Sum.inl) at ha
  rwa [lineComponentPairIdeal_comap_left Q Q'] at ha

/-- No original right component relation is lost in the actual pair quotient. -/
theorem linePairRightCoordinateHom_injective : Function.Injective (linePairRightCoordinateHom Q Q') := by
  apply (injective_iff_map_eq_zero _).mpr
  intro a ha
  obtain ⟨P, rfl⟩ := Ideal.Quotient.mk_surjective a
  rw [linePairRightCoordinateHom_mk, Ideal.Quotient.eq_zero_iff_mem] at ha
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  change P ∈ (lineComponentPairIdeal Q Q').comap (MvPolynomial.rename Sum.inr) at ha
  rwa [lineComponentPairIdeal_comap_right Q Q'] at ha

/-- The two original component coordinate images generate the entire
actual pair-coordinate quotient. -/
theorem linePairCoordinateImages_generate :
    Algebra.adjoin K ((linePairLeftCoordinateHom Q Q').range ∪
      (linePairRightCoordinateHom Q Q').range : Set PairRing) = ⊤ := by
  let S := Algebra.adjoin K ((linePairLeftCoordinateHom Q Q').range ∪
    (linePairRightCoordinateHom Q Q').range : Set PairRing)
  apply top_unique
  intro a ha
  clear ha
  obtain ⟨P, rfl⟩ := Ideal.Quotient.mk_surjective a
  induction P using MvPolynomial.induction_on with
  | C c => exact S.algebraMap_mem c
  | add P R hP hR => rw [map_add]; exact S.add_mem hP hR
  | mul_X P ij hP =>
    rw [map_mul]
    apply S.mul_mem hP
    cases ij with
    | inl ij =>
      apply Algebra.subset_adjoin
      refine Or.inl ⟨Ideal.Quotient.mk Q (X ij), ?_⟩
      change linePairLeftCoordinateHom Q Q' (Ideal.Quotient.mk Q (X ij)) = _
      rw [linePairLeftCoordinateHom_mk, rename_X]
    | inr ij =>
      apply Algebra.subset_adjoin
      refine Or.inr ⟨Ideal.Quotient.mk Q' (X ij), ?_⟩
      change linePairRightCoordinateHom Q Q' (Ideal.Quotient.mk Q' (X ij)) = _
      rw [linePairRightCoordinateHom_mk, rename_X]

/-- If both actual component function fields have dimension one, the
actual pair-coordinate ring has transcendence degree at most two. -/
theorem lineComponentPair_trdeg_le_two
    (hQ : Algebra.trdeg K (FractionRing LeftRing) = 1)
    (hQ' : Algebra.trdeg K (FractionRing RightRing) = 1) :
    Algebra.trdeg K PairRing ≤ 2 := by
  have hleft : Algebra.trdeg K (linePairLeftCoordinateHom Q Q').range ≤ 1 := by
    apply (trdeg_le_of_surjective (linePairLeftCoordinateHom Q Q').rangeRestrict
      (linePairLeftCoordinateHom Q Q').rangeRestrict_surjective).trans
    exact (trdeg_le_of_injective (IsScalarTower.toAlgHom K LeftRing (FractionRing LeftRing))
      (IsFractionRing.injective LeftRing (FractionRing LeftRing))).trans_eq hQ
  have hright : Algebra.trdeg K (linePairRightCoordinateHom Q Q').range ≤ 1 := by
    apply (trdeg_le_of_surjective (linePairRightCoordinateHom Q Q').rangeRestrict
      (linePairRightCoordinateHom Q Q').rangeRestrict_surjective).trans
    exact (trdeg_le_of_injective (IsScalarTower.toAlgHom K RightRing (FractionRing RightRing))
      (IsFractionRing.injective RightRing (FractionRing RightRing))).trans_eq hQ'
  have he := adjoin_union_trdeg_le_sum (K := K)
    ((linePairLeftCoordinateHom Q Q').range : Set PairRing)
    ((linePairRightCoordinateHom Q Q').range : Set PairRing)
  rw [linePairCoordinateImages_generate,
    (Subalgebra.topEquiv (R := K) (A := PairRing)).trdeg_eq, Algebra.adjoin_eq, Algebra.adjoin_eq] at he
  exact (he.trans (add_le_add hleft hright)).trans_eq (by norm_num)

end DimensionFourDependence
