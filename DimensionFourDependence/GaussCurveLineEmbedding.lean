import DimensionFourDependence.LocalizedRatioRelations
import DimensionFourDependence.CurveCoordinateSpecialization
import DimensionFourDependence.ActualGaussSourceLine

/-! # Embedding the actual Gauss curve function field into a source line

Localization transfers every original relation to the constructed source
line. Its transcendental normal ratio prevents a dimension drop on the
actual Gauss curve. The resulting function-field embedding sends every
actual normal ratio to its actual line-restricted rational function.
-/

namespace DimensionFourDependence

open MvPolynomial

variable {K : Type*} [Field K] {n : ℕ}

/-- The actual source-line substitution followed by passage to the
line's one-variable rational-function field. -/
noncomputable def sourceLineRationalSpecialization (p q : Fin n → K) :
    MvPolynomial (Fin n) K →ₐ[K] RatFunc K :=
  (IsScalarTower.toAlgHom K (Polynomial K) (RatFunc K)).comp (aeval (sourcePointLinePolynomial p q))

/-- This specialization evaluates each original polynomial as its
actual source-line polynomial in the line's function field. -/
theorem sourceLineRationalSpecialization_apply (p q : Fin n → K) (P : MvPolynomial (Fin n) K) :
    sourceLineRationalSpecialization p q P =
      algebraMap (Polynomial K) (RatFunc K) (sourceLinePolynomialPullback p q P) := rfl

/-- The actual source-line ratios in a chosen nonzero polynomial chart. -/
noncomputable def sourceLineRationalRatios (N : Fin n → MvPolynomial (Fin n) K)
    (a : Fin n) (p q : Fin n → K) : Fin n → RatFunc K :=
  fun i => sourceLineRationalSpecialization p q (N i) / sourceLineRationalSpecialization p q (N a)

/-- All original projective coordinate relations survive actual
source-line restriction if the pivot polynomial survives on that line. -/
theorem polynomial_projective_ratio_relations_on_source_line
    (N : Fin n → MvPolynomial (Fin n) K) (a : Fin n) (ha : N a ≠ 0)
    (p q : Fin n → K) (hline : sourceLinePolynomialPullback p q (N a) ≠ 0)
    (P : MvPolynomial (Fin n) K)
    (hP : aeval (fun i => algebraMap (MvPolynomial (Fin n) K) (FractionRing (MvPolynomial (Fin n) K)) (N i) /
      algebraMap (MvPolynomial (Fin n) K) (FractionRing (MvPolynomial (Fin n) K)) (N a)) P = 0) :
    aeval (sourceLineRationalRatios N a p q) P = 0 := by
  let f := IsScalarTower.toAlgHom K (MvPolynomial (Fin n) K) (FractionRing (MvPolynomial (Fin n) K))
  have hf : Function.Injective f := IsFractionRing.injective _ _
  have hfa : f (N a) ≠ 0 := by
    intro hz
    apply ha
    apply hf
    simpa only [map_zero] using hz
  have hga : sourceLineRationalSpecialization p q (N a) ≠ 0 := by
    intro hz
    apply hline
    apply IsFractionRing.injective (Polynomial K) (RatFunc K)
    simpa only [sourceLineRationalSpecialization_apply, map_zero] using hz
  exact ratio_polynomial_relations_specialize f hf (sourceLineRationalSpecialization p q)
    (N a) hfa hga N P hP

universe u

/-- The actual one-dimensional Gauss image supplies a constructed
original-field source line and an embedding of its entire function field
in that line's rational-function field, preserving every actual normal
ratio. No source-line field injectivity is assumed. -/
theorem exists_actual_gauss_curve_source_line_field_embedding
    {K : Type u} [Field K] [CharZero K]
    (H : Fin 4 → MvPolynomial (Fin 4) K) (I : ImageRelationWitness H)
    (hGauss : gaussImageDimension H I = 1) :
    ∃ p q : Fin 4 → K,
      sourceLinePolynomialPullback p q (imageRelationNormal H I.equation (imageNormalPivot H I)) ≠ 0 ∧
      ∃ f : projectiveRatioField (K := K) (rationalImageNormal H I.equation) (imageNormalPivot H I) →ₐ[K] RatFunc K,
        ∀ j, f (fullOutputCoordinate (K := K)
          (fun i => rationalImageNormal H I.equation i / rationalImageNormal H I.equation (imageNormalPivot H I)) j) =
          sourceLineRationalRatios (imageRelationNormal H I.equation) (imageNormalPivot H I) p q j := by
  have hnonzero : gaussImageDimension H I ≠ 0 := by rw [hGauss]; norm_num
  obtain ⟨i, p, q, _, _, hline, ht⟩ := exists_actual_gauss_source_line_transcendental_ratio H I hnonzero
  have hpivot : imageRelationNormal H I.equation (imageNormalPivot H I) ≠ 0 := by
    intro hz
    exact imageNormalPivot_ne_zero H I (by simp only [rationalImageNormal, hz, map_zero])
  let x : Fin 4 → FractionRing (MvPolynomial (Fin 4) K) :=
    fun j => rationalImageNormal H I.equation j / rationalImageNormal H I.equation (imageNormalPivot H I)
  let y := sourceLineRationalRatios (imageRelationNormal H I.equation) (imageNormalPivot H I) p q
  have hdim : Algebra.trdeg K (fullOutputField (K := K) x) = 1 := hGauss
  have hrel : ∀ P : MvPolynomial (Fin 4) K, aeval x P = 0 → aeval y P = 0 := by
    intro P hP
    exact polynomial_projective_ratio_relations_on_source_line (imageRelationNormal H I.equation)
      (imageNormalPivot H I) hpivot p q hline P hP
  have hy : Transcendental K (y i) := ht
  obtain ⟨f, hf⟩ := exists_curve_function_field_embedding_of_specialization x y hdim hrel i hy
  exact ⟨p, q, hline, f, hf⟩

end DimensionFourDependence
