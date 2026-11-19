import DimensionFourDependence.GeneratedFieldDimension

/-! # A surface family with no divisor image has a fixed curve point field -/

namespace DimensionFourDependence

universe u

variable {K F G : Type u} [Field K] [Field F] [Field G]
  [Algebra K F] [Algebra K G] [Algebra F G] [IsScalarTower K F G]

/-- A two-dimensional family generated algebraically by a point
field and one parameter has point-field dimension one whenever that
dimension is not two. Its parameter remains transcendental over the point field. -/
theorem surface_point_field_dimension_one_and_parameter_transcendental_of_ne_two
    (t : G) [Algebra.IsAlgebraic (IntermediateField.adjoin F {t}) G]
    (hG : Algebra.trdeg K G = 2) (hF : Algebra.trdeg K F ≠ 2) :
    Algebra.trdeg K F = 1 ∧ Transcendental F t := by
  let J := IntermediateField.adjoin F {t}
  let : IsScalarTower K J G := IsScalarTower.of_algebraMap_eq (by
    intro c
    rw [IsScalarTower.algebraMap_apply K F J, ← IsScalarTower.algebraMap_apply F J G]
    exact IsScalarTower.algebraMap_apply K F G c)
  have hJG : Algebra.trdeg J G = 0 := trdeg_eq_zero
  have hFJ : Algebra.trdeg F J ≤ 1 := generatedField_singleton_trdeg_le_one t
  have hFpos : Algebra.trdeg K F ≠ 0 := by
    intro hz
    have hKJ := trdeg_add_eq (A := J) K F
    have hKJle : Algebra.trdeg K J ≤ 1 := by
      rw [← hKJ, hz, zero_add]
      exact hFJ
    have hKJG := trdeg_add_eq (A := G) K J
    have hKGle : Algebra.trdeg K G ≤ 1 := by
      rw [← hKJG, hJG, add_zero]
      exact hKJle
    have hbad : (2 : Cardinal) ≤ 1 := hG.symm.trans_le hKGle
    norm_num at hbad
  have hFle : Algebra.trdeg K F ≤ 2 :=
    (trdeg_le_of_injective (IsScalarTower.toAlgHom K F G) (algebraMap F G).injective).trans_eq hG
  have hFlt : Algebra.trdeg K F < 2 := lt_of_le_of_ne hFle hF
  have hFle1 : Algebra.trdeg K F ≤ 1 :=
    (Cardinal.lt_natCast_add_one_iff (n := 1)).mp (by convert hFlt using 1; norm_num)
  have hFdim : Algebra.trdeg K F = 1 := le_antisymm hFle1 (Cardinal.one_le_iff_ne_zero.mpr hFpos)
  refine ⟨hFdim, ?_⟩
  intro ht
  let : Algebra.IsAlgebraic F J := IntermediateField.isAlgebraic_adjoin_simple ht.isIntegral
  have hFJzero : Algebra.trdeg F J = 0 := trdeg_eq_zero
  have hFJG := trdeg_add_eq (A := G) F J
  rw [hFJzero, hJG, zero_add] at hFJG
  have hKFG := trdeg_add_eq (A := G) K F
  rw [hFdim, ← hFJG, add_zero, hG] at hKFG
  norm_num at hKFG

end DimensionFourDependence
