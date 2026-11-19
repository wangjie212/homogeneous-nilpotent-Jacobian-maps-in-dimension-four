import DimensionFourDependence.SourceLineRatio
import DimensionFourDependence.GaussImageDimension

/-! # A source line on which the actual Gauss coordinates remain nonconstant

A positive-dimensional actual normal-ratio field has an entry not
proportional over the original field to its nonzero pivot. The checked
original-field source-point selection and source-line restriction then
give a transcendental actual normal ratio on a constructed source line.
-/

namespace DimensionFourDependence

open MvPolynomial

variable {K : Type*} [Field K] {n : ℕ}

/-- If the actual polynomial projective ratio field has nonzero
dimension, one coordinate is not constantly proportional to the pivot. -/
theorem exists_nonproportional_polynomial_projective_coordinate
    (N : Fin n → MvPolynomial (Fin n) K) (a : Fin n) (ha : N a ≠ 0)
    (hdim : Algebra.trdeg K (projectiveRatioField (K := K)
      (fun i => algebraMap (MvPolynomial (Fin n) K) (FractionRing (MvPolynomial (Fin n) K)) (N i)) a) ≠ 0) :
    ∃ i : Fin n, ¬ ∃ c : K, N i = c • N a := by
  by_contra hn
  push Not at hn
  choose c hc using hn
  let ν : Fin n → FractionRing (MvPolynomial (Fin n) K) :=
    fun i => algebraMap (MvPolynomial (Fin n) K) _ (N i)
  have hν : ν a ≠ 0 := by
    intro hz
    apply ha
    apply IsFractionRing.injective (MvPolynomial (Fin n) K) (FractionRing (MvPolynomial (Fin n) K))
    simpa only [map_zero] using hz
  have he (i : Fin n) : ν i / ν a = algebraMap K (FractionRing (MvPolynomial (Fin n) K)) (c i) := by
    change algebraMap (MvPolynomial (Fin n) K) (FractionRing (MvPolynomial (Fin n) K)) (N i) / ν a = _
    rw [hc i, MvPolynomial.smul_eq_C_mul, map_mul]
    exact mul_div_cancel_right₀ _ hν
  have hR : projectiveRatioField (K := K) ν a = ⊥ := by
    apply bot_unique
    apply IntermediateField.adjoin_le_iff.mpr
    rintro _ ⟨i, rfl⟩
    change ν i / ν a ∈ (⊥ : IntermediateField K (FractionRing (MvPolynomial (Fin n) K)))
    rw [he i]
    exact (⊥ : IntermediateField K (FractionRing (MvPolynomial (Fin n) K))).algebraMap_mem (c i)
  apply hdim
  change Algebra.trdeg K (projectiveRatioField (K := K) ν a) = 0
  rw [hR]
  exact trdeg_eq_zero

variable [CharZero K]

/-- A nonzero-dimensional actual Gauss image supplies an actual
original-field source line with a nonzero normal pivot and a
transcendental line-restricted normal ratio. -/
theorem exists_actual_gauss_source_line_transcendental_ratio
    (H : Fin 4 → MvPolynomial (Fin 4) K) (I : ImageRelationWitness H)
    (hGauss : gaussImageDimension H I ≠ 0) :
    ∃ (i : Fin 4) (p q : Fin 4 → K),
      MvPolynomial.eval p (imageRelationNormal H I.equation (imageNormalPivot H I)) ≠ 0 ∧
      MvPolynomial.eval q (imageRelationNormal H I.equation (imageNormalPivot H I)) ≠ 0 ∧
      sourceLinePolynomialPullback p q (imageRelationNormal H I.equation (imageNormalPivot H I)) ≠ 0 ∧
      Transcendental K
        (algebraMap (Polynomial K) (RatFunc K) (sourceLinePolynomialPullback p q (imageRelationNormal H I.equation i)) /
          algebraMap (Polynomial K) (RatFunc K)
            (sourceLinePolynomialPullback p q (imageRelationNormal H I.equation (imageNormalPivot H I)))) := by
  have hpivot : imageRelationNormal H I.equation (imageNormalPivot H I) ≠ 0 := by
    intro hz
    exact imageNormalPivot_ne_zero H I (by simp only [rationalImageNormal, hz, map_zero])
  obtain ⟨i, hi⟩ := exists_nonproportional_polynomial_projective_coordinate
    (imageRelationNormal H I.equation) (imageNormalPivot H I) hpivot hGauss
  obtain ⟨p, q, hp, hq, hg, ht⟩ := exists_source_line_transcendental_ratio
    (imageRelationNormal H I.equation i) (imageRelationNormal H I.equation (imageNormalPivot H I)) hpivot hi
  exact ⟨i, p, q, hp, hq, hg, ht⟩

end DimensionFourDependence
