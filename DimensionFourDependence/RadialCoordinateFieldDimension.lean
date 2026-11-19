import DimensionFourDependence.ProjectiveOutputField
import DimensionFourDependence.ProjectiveRatioEmbedding
import DimensionFourDependence.VertexParameterTranscendence
import DimensionFourDependence.RationalParameterDerivation

/-! # An independent radial coordinate raises the dimension of a projective direction -/

namespace DimensionFourDependence

universe u

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000

variable {K F : Type u} [Field K] [Field F] [Algebra K F] {n : ℕ}

/-- Every coordinate is recovered from its actual projective ratio
and one specified nonzero original coordinate, for any finite tuple. -/
theorem projective_ratios_adjoin_coordinate_eq_generated_field
    (y : Fin n → F) (j : Fin n) (hj : y j ≠ 0) :
    (IntermediateField.adjoin (projectiveRatioField (K := K) y j) {y j}).restrictScalars K =
      IntermediateField.adjoin K (Set.range y) := by
  rw [projectiveRatioField, IntermediateField.adjoin_adjoin_left]
  apply le_antisymm
  · apply IntermediateField.adjoin_le_iff.mpr
    intro z hz
    rcases hz with ⟨i, rfl⟩ | rfl
    · exact (IntermediateField.adjoin K (Set.range y)).div_mem
        (IntermediateField.subset_adjoin K _ ⟨i, rfl⟩)
        (IntermediateField.subset_adjoin K _ ⟨j, rfl⟩)
    · exact IntermediateField.subset_adjoin K _ ⟨j, rfl⟩
  · apply IntermediateField.adjoin_le_iff.mpr
    rintro _ ⟨i, rfl⟩
    rw [← div_mul_cancel₀ (y i) hj]
    exact (IntermediateField.adjoin K (Set.range (fun i => y i / y j) ∪ {y j})).mul_mem
      (IntermediateField.subset_adjoin K _ (Or.inl ⟨i, rfl⟩))
      (IntermediateField.subset_adjoin K _ (Or.inr rfl))

/-- A specified coordinate transcendental over the actual ratio
field adds exactly one to the generated coordinate-field dimension. -/
theorem coordinate_field_trdeg_eq_projective_add_one
    (y : Fin n → F) (j : Fin n) (hj : y j ≠ 0)
    (ht : Transcendental (projectiveRatioField (K := K) y j) (y j)) :
    Algebra.trdeg K (IntermediateField.adjoin K (Set.range y)) =
      Algebra.trdeg K (projectiveRatioField (K := K) y j) + 1 := by
  let R := projectiveRatioField (K := K) y j
  let J := IntermediateField.adjoin R {y j}
  have hd : Algebra.trdeg R J = 1 :=
    generatedField_singleton_trdeg_one_of_transcendental (K := R) (y j) ht
  let : FaithfulSMul K R :=
    (faithfulSMul_iff_algebraMap_injective K R).mpr (algebraMap K R).injective
  let : FaithfulSMul R J :=
    (faithfulSMul_iff_algebraMap_injective R J).mpr (algebraMap R J).injective
  have he := trdeg_add_eq (A := J) K R
  rw [hd] at he
  calc
    _ = Algebra.trdeg K (J.restrictScalars K) := by
      rw [projective_ratios_adjoin_coordinate_eq_generated_field y j hj]
    _ = Algebra.trdeg K J := rfl
    _ = _ := he.symm

variable [CharZero K] {E : Type u} [Field E] [Algebra K E]

/-- A nonconstant projective direction, multiplied by one independent
radial variable, generates a field of dimension at least two over the
original constants. The radial derivative supplies transcendence over
the whole actual projective ratio field. -/
theorem nonconstant_direction_independent_radial_field_dimension_ge_two
    (A : Fin n → E) (j : Fin n) (hj : A j ≠ 0)
    (hdim : Algebra.trdeg K (projectiveRatioField (K := K) A j) ≠ 0) :
    2 ≤ Algebra.trdeg K (IntermediateField.adjoin K
      (Set.range (fun i => (RatFunc.X : RatFunc E) * RatFunc.C (A i)))) := by
  let y : Fin n → RatFunc E := fun i => RatFunc.X * RatFunc.C (A i)
  let D : Derivation K (RatFunc E) (RatFunc E) := (rationalParameterDerivative E).restrictScalars K
  let f : E →ₐ[K] RatFunc E := IsScalarTower.toAlgHom K E (RatFunc E)
  have hjC : RatFunc.C (A j) ≠ 0 := (map_ne_zero RatFunc.C).mpr hj
  have hyj : y j ≠ 0 := mul_ne_zero RatFunc.X_ne_zero hjC
  have hratio (i : Fin n) : y i / y j = RatFunc.C (A i / A j) := by
    change (RatFunc.X * RatFunc.C (A i)) / (RatFunc.X * RatFunc.C (A j)) = _
    rw [map_div₀]
    field_simp [RatFunc.X_ne_zero, hjC]
  have hconst (c : E) : D (RatFunc.C c) = 0 := by
    change rationalParameterDerivative E (algebraMap E (RatFunc E) c) = 0
    exact (rationalParameterDerivative E).map_algebraMap c
  have hkill (i : Fin n) : D (y i / y j) = 0 := by rw [hratio]; exact hconst _
  have hDyj : D (y j) = RatFunc.C (A j) := by
    change rationalParameterDerivative E (RatFunc.X * algebraMap E (RatFunc E) (A j)) = _
    rw [Derivation.leibniz, rationalParameterDerivative_X,
      (rationalParameterDerivative E).map_algebraMap]
    simp only [smul_eq_mul, mul_zero, mul_one, zero_add]
    rfl
  have ht : Transcendental (projectiveRatioField (K := K) y j) (y j) :=
    nonzero_derivation_value_transcendental_over_coordinate_field D
      (fun i => y i / y j) hkill (y j) (by rw [hDyj]; exact hjC)
  have hfun : (fun i => y i / y j) = (fun i => (f ∘ A) i / (f ∘ A) j) := by
    funext i
    rw [hratio, map_div₀]
    rfl
  have hdimy : Algebra.trdeg K (projectiveRatioField (K := K) y j) ≠ 0 := by
    change Algebra.trdeg K (IntermediateField.adjoin K (Set.range (fun i => y i / y j))) ≠ 0
    rw [hfun]
    exact (projective_ratio_positive_dimension_field_embedding_iff f A j).mpr hdim
  have hone : 1 ≤ Algebra.trdeg K (projectiveRatioField (K := K) y j) :=
    Cardinal.one_le_iff_ne_zero.mpr hdimy
  change 2 ≤ Algebra.trdeg K (IntermediateField.adjoin K (Set.range y))
  rw [coordinate_field_trdeg_eq_projective_add_one y j hyj ht]
  calc
    (2 : Cardinal) = 1 + 1 := by norm_num
    _ ≤ Algebra.trdeg K (projectiveRatioField (K := K) y j) + 1 := by
      simpa only [add_comm] using add_le_add_right hone 1

end DimensionFourDependence
