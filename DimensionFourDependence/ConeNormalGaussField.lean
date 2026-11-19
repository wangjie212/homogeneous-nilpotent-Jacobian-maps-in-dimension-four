import DimensionFourDependence.ProjectiveRatioEmbedding
import DimensionFourDependence.NonconstantTangentLineAlgebraicity

/-! # The actual cone vertex retains a positive-dimensional ternary Gauss image

Dropping a vanishing fourth normal coordinate preserves the entire
actual projective normal-ratio field. Gauss dimension one therefore
constructs a nonzero ternary normal chart of dimension one. Its positive
dimension survives every actual source-field embedding, supplying the
nonconstant normal image used by the moving-line intersection theorem.
The specified fourth-axis vertex condition remains explicit.
-/

namespace DimensionFourDependence

universe u

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

/-- A zero last normal coordinate contributes no generator to the
entire actual projective normal-ratio field. -/
theorem projectiveRatioField_drop_zero_last_normal
    (nu : Fin 4 → F) (hvertex : nu (Fin.last 3) = 0) (j : Fin 3) :
    projectiveRatioField (K := K) nu j.castSucc =
      projectiveRatioField (K := K) (fun i : Fin 3 => nu i.castSucc) j := by
  apply le_antisymm
  · apply IntermediateField.adjoin_le_iff.mpr
    rintro z ⟨i, rfl⟩
    refine Fin.lastCases ?_ (fun i => ?_) i
    · have hz : nu (Fin.last 3) / nu j.castSucc = 0 := by rw [hvertex, zero_div]
      change nu (Fin.last 3) / nu j.castSucc ∈
        projectiveRatioField (K := K) (fun i : Fin 3 => nu i.castSucc) j
      rw [hz]
      exact (projectiveRatioField (K := K) (fun i : Fin 3 => nu i.castSucc) j).zero_mem
    · exact IntermediateField.subset_adjoin K _ ⟨i, rfl⟩
  · apply IntermediateField.adjoin_le_iff.mpr
    rintro z ⟨i, rfl⟩
    exact IntermediateField.subset_adjoin K _ ⟨i.castSucc, rfl⟩

/-- A common nonzero normal scalar preserves the entire actual
projective ratio field, including charts with zero numerator entries. -/
theorem projectiveRatioField_nonzero_scalar_multiple {n : ℕ}
    (nu : Fin n → F) (c : F) (hc : c ≠ 0) (j : Fin n) :
    projectiveRatioField (K := K) (fun i => c * nu i) j =
      projectiveRatioField (K := K) nu j := by
  have hcoords : (fun i : Fin n => (c * nu i) / (c * nu j)) =
      (fun i : Fin n => nu i / nu j) := by
    funext i
    exact mul_div_mul_left (nu i) (nu j) hc
  exact congrArg (fun x : Fin n → F => IntermediateField.adjoin K (Set.range x)) hcoords

omit [Field F] [Algebra K F] in
/-- The original dimension-one Gauss image and specified vertex
construct a genuine original ternary normal chart of dimension one. -/
theorem original_vertex_gauss_dimension_one_constructs_ternary_normal_chart
    (H : Fin 4 → MvPolynomial (Fin 4) K) (I : ImageRelationWitness H)
    (hGauss : gaussImageDimension H I = 1)
    (hvertex : rationalImageNormal H I.equation (Fin.last 3) = 0) :
    ∃ j : Fin 3, rationalImageNormal H I.equation j.castSucc ≠ 0 ∧
      Algebra.trdeg K (projectiveRatioField (K := K)
        (fun i : Fin 3 => rationalImageNormal H I.equation i.castSucc) j) = 1 := by
  let N := rationalImageNormal H I.equation
  have hfirst : (fun i : Fin 3 => N i.castSucc) ≠ 0 := by
    intro hz
    have hN : N = 0 := by
      funext i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · exact hvertex
      · exact congrFun hz j
    apply imageNormalPivot_ne_zero H I
    exact congrFun hN (imageNormalPivot H I)
  obtain ⟨j, hj⟩ : ∃ j : Fin 3, N j.castSucc ≠ 0 := by
    simpa only [ne_eq, funext_iff, Pi.zero_apply, not_forall] using hfirst
  have he := projectiveRatioField_chart_eq (K := K) N
    (imageNormalPivot H I) j.castSucc (imageNormalPivot_ne_zero H I) hj
  have hdim : Algebra.trdeg K (projectiveRatioField (K := K) N j.castSucc) = 1 := by
    rw [← he]
    exact hGauss
  rw [projectiveRatioField_drop_zero_last_normal N hvertex j] at hdim
  exact ⟨j, hj, hdim⟩

/-- Every actual source-field realization retains a nonzero ternary
normal chart with positive-dimensional original projective image. -/
theorem original_vertex_gauss_normal_embedding_positive_ternary_chart
    (H : Fin 4 → MvPolynomial (Fin 4) K) (I : ImageRelationWitness H)
    (hGauss : gaussImageDimension H I = 1)
    (hvertex : rationalImageNormal H I.equation (Fin.last 3) = 0)
    (f : FractionRing (MvPolynomial (Fin 4) K) →ₐ[K] F) :
    ∃ j : Fin 3, f (rationalImageNormal H I.equation j.castSucc) ≠ 0 ∧
      Algebra.trdeg K (projectiveRatioField (K := K)
        (fun i : Fin 3 => f (rationalImageNormal H I.equation i.castSucc)) j) ≠ 0 := by
  obtain ⟨j, hj, hdim⟩ := original_vertex_gauss_dimension_one_constructs_ternary_normal_chart
    H I hGauss hvertex
  have hj' : f (rationalImageNormal H I.equation j.castSucc) ≠ 0 := by
    intro hz
    apply hj
    apply f.injective
    exact hz.trans (map_zero f).symm
  have hdim' : Algebra.trdeg K (projectiveRatioField (K := K)
      (fun i : Fin 3 => rationalImageNormal H I.equation i.castSucc) j) ≠ 0 := by
    rw [hdim]
    exact one_ne_zero
  exact ⟨j, hj', (projective_ratio_positive_dimension_field_embedding_iff f _ j).mpr hdim'⟩

/-- Gauss dimension one supplies the genuine moving ternary normal
image over every specified compatible coefficient realization, allowing
the common nonzero projective normal scalar from the actual chart. -/
theorem original_vertex_gauss_compatible_normal_realization_positive
    (H : Fin 4 → MvPolynomial (Fin 4) K) (I : ImageRelationWitness H)
    (hGauss : gaussImageDimension H I = 1)
    (hvertex : rationalImageNormal H I.equation (Fin.last 3) = 0)
    (L : Type*) [Field L] [Algebra K L]
    (f : FractionRing (MvPolynomial (Fin 4) K) →ₐ[K] F) (g : L →ₐ[K] F)
    (nu : Fin 3 → L) (c : F) (hc : c ≠ 0)
    (hrealize : ∀ i : Fin 3, g (nu i) = c * f (rationalImageNormal H I.equation i.castSucc)) :
    ∃ j : Fin 3, nu j ≠ 0 ∧
      Algebra.trdeg K (projectiveRatioField (K := K) nu j) ≠ 0 := by
  obtain ⟨j, hj, hdim⟩ := original_vertex_gauss_normal_embedding_positive_ternary_chart
    H I hGauss hvertex f
  have hcoords : g ∘ nu =
      (fun i : Fin 3 => c * f (rationalImageNormal H I.equation i.castSucc)) := funext hrealize
  have htarget : Algebra.trdeg K (projectiveRatioField (K := K) (g ∘ nu) j) ≠ 0 := by
    rw [hcoords, projectiveRatioField_nonzero_scalar_multiple _ c hc j]
    exact hdim
  have hjg : g (nu j) ≠ 0 := by
    rw [hrealize]
    exact mul_ne_zero hc hj
  have hjnu : nu j ≠ 0 := by
    intro hz
    exact hjg ((congrArg g hz).trans (map_zero g))
  exact ⟨j, hjnu, (projective_ratio_positive_dimension_field_embedding_iff g nu j).mp htarget⟩

/-- For an actual original Gauss-dimension-one cone normal realization,
a proper original ternary equation forces the actual incident direction
to be algebraic and to generate a finite ruling-field extension. The
normal-image dimension, genuine line restriction and all coordinate
algebraicity conclusions are derived from the original map data. -/
theorem original_vertex_gauss_realized_direction_algebraic_finite [Infinite K]
    (H : Fin 4 → MvPolynomial (Fin 4) K) (I : ImageRelationWitness H)
    (hGauss : gaussImageDimension H I = 1)
    (hvertex : rationalImageNormal H I.equation (Fin.last 3) = 0)
    (L E : Type u) [Field L] [Field E] [Algebra K L] [Algebra L E]
    [Algebra K E] [IsScalarTower K L E]
    (f : FractionRing (MvPolynomial (Fin 4) K) →ₐ[K] F) (g : L →ₐ[K] F)
    (nu : Fin 3 → L) (c : F) (hc : c ≠ 0)
    (hrealize : ∀ i : Fin 3, g (nu i) = c * f (rationalImageNormal H I.equation i.castSucc))
    (Q : MvPolynomial (Fin 3) K) (hQ0 : Q ≠ 0) {D : ℕ} (hQ : Q.IsHomogeneous D)
    (A : Fin 3 → E) (hA : A ≠ 0)
    (hincidence : ∑ i : Fin 3, algebraMap L E (nu i) * A i = 0)
    (hzero : MvPolynomial.aeval A Q = 0) (j : Fin 3) (hj : A j ≠ 0) :
    (∀ i : Fin 3, IsAlgebraic L (A i / A j)) ∧
      Module.Finite L (IntermediateField.adjoin L (Set.range (fun i => A i / A j))) := by
  obtain ⟨k, hk, hdim⟩ := original_vertex_gauss_compatible_normal_realization_positive
    H I hGauss hvertex L f g nu c hc hrealize
  exact ⟨positive_dimensional_normal_original_direction_ratios_isAlgebraic
      nu k hk hdim Q hQ0 hQ A hA hincidence hzero j hj,
    positive_dimensional_normal_original_direction_field_finite
      nu k hk hdim Q hQ0 hQ A hA hincidence hzero j hj⟩

end DimensionFourDependence
