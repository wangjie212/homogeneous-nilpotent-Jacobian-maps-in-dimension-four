import DimensionFourDependence.ProjectiveCovectorTranscendence

/-! # Projective normal-image nonconstancy under coefficient embeddings

The actual ratio field has dimension zero exactly when all its original
coordinate ratios are algebraic. A coefficient-field embedding both
preserves and reflects those algebraicity statements. Consequently the
nonconstant normal image survives every compatible field realization.
-/

namespace DimensionFourDependence

variable {K L F : Type*} [Field K] [Field L] [Field F] [Algebra K L] [Algebra K F]
    {n : ℕ}

/-- Zero dimension of the entire actual original ratio field is
equivalent to algebraicity of all its original coordinate ratios. -/
theorem projective_ratio_dimension_zero_iff_coordinate_algebraic
    (nu : Fin n → L) (j : Fin n) :
    Algebra.trdeg K (projectiveRatioField (K := K) nu j) = 0 ↔
      ∀ i : Fin n, IsAlgebraic K (nu i / nu j) := by
  change Algebra.trdeg K (IntermediateField.adjoin K (Set.range (fun i => nu i / nu j))) = 0 ↔ _
  rw [trdeg_eq_zero_iff,
    IntermediateField.isAlgebraic_adjoin_iff_isAlgebraic (F := K) (E := L)]
  simp only [Set.forall_mem_range]

/-- An actual coefficient-field embedding preserves and reflects
nonconstancy of the entire original projective normal image. -/
theorem projective_ratio_positive_dimension_field_embedding_iff
    (f : L →ₐ[K] F) (nu : Fin n → L) (j : Fin n) :
    Algebra.trdeg K (projectiveRatioField (K := K) (f ∘ nu) j) ≠ 0 ↔
      Algebra.trdeg K (projectiveRatioField (K := K) nu j) ≠ 0 := by
  apply not_congr
  rw [projective_ratio_dimension_zero_iff_coordinate_algebraic,
    projective_ratio_dimension_zero_iff_coordinate_algebraic]
  apply forall_congr'
  intro i
  change IsAlgebraic K (f (nu i) / f (nu j)) ↔ IsAlgebraic K (nu i / nu j)
  rw [← map_div₀]
  exact isAlgebraic_algHom_iff f f.injective

end DimensionFourDependence
