import DimensionFourDependence.ProjectivePointHilbertEvaluation
import DimensionFourDependence.GeometricHilbertBound

/-! # Enlarging compatible projective coefficients cannot increase the Hilbert function -/

namespace DimensionFourDependence

open MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000

variable {K L F G σ : Type*} [Field K] [Field L] [Field F] [Field G]
  [Algebra K F] [Algebra K L] [Algebra L G] [Algebra K G] [IsScalarTower K L G]

/-- A compatible source-field embedding retains every original
homogeneous relation after extending its coefficient field. -/
theorem projectiveFieldPointIdeal_extended_le_of_source_embedding
    (f : F →ₐ[K] G) (x : σ → F) :
    extendCoefficientIdeal L (projectiveFieldPointIdeal (E := K) x).toIdeal ≤
      (projectiveFieldPointIdeal (E := L) (f ∘ x)).toIdeal := by
  have heval : (aeval (f ∘ x) : MvPolynomial σ K →ₐ[K] G) = f.comp (aeval x) := by
    apply MvPolynomial.algHom_ext
    intro i
    simp only [aeval_X, AlgHom.comp_apply, Function.comp_apply]
  apply Ideal.map_le_iff_le_comap.mpr
  intro P hP
  change MvPolynomial.map (algebraMap K L) P ∈
    (projectiveFieldPointIdeal (E := L) (f ∘ x)).toIdeal
  have hzero := (projectiveFieldPointIdeal_mem_iff_components x P).mp hP
  rw [← sum_homogeneousComponent P, map_sum]
  apply (projectiveFieldPointIdeal (E := L) (f ∘ x)).toIdeal.sum_mem
  intro d _hd
  apply (projectiveFieldPointIdeal_mem_homogeneous _ _
    ((homogeneousComponent_isHomogeneous d P).map (algebraMap K L))).mpr
  rw [aeval_map_coefficients, heval, AlgHom.comp_apply, hzero d, map_zero]

/-- Compatible extension of the coefficient field can only reduce
the dimension of each original projective homogeneous coordinate space. -/
theorem projectiveHilbertFunction_point_le_of_source_embedding [Finite σ]
    (f : F →ₐ[K] G) (x : σ → F) (n : ℕ) :
    projectiveHilbertFunction (projectiveFieldPointIdeal (E := L) (f ∘ x)).toIdeal n ≤
      projectiveHilbertFunction (projectiveFieldPointIdeal (E := K) x).toIdeal n := by
  calc
    _ ≤ projectiveHilbertFunction
        (extendCoefficientIdeal L (projectiveFieldPointIdeal (E := K) x).toIdeal) n :=
      projectiveHilbertFunction_antitone
        (projectiveFieldPointIdeal_extended_le_of_source_embedding (L := L) f x) n
    _ = _ := projectiveHilbertFunction_field_extension L _ n

/-- Every compatible projective source realization obeys the
original positive curve degree bound after extending coefficients. -/
theorem projectiveCurveDegree_le_of_source_embedding [Finite σ]
    (f : F →ₐ[K] G) (x : σ → F) {D D' : ℕ}
    (hD : HasCurveHilbertDegree (projectiveFieldPointIdeal (E := K) x).toIdeal D)
    (hD' : HasCurveHilbertDegree (projectiveFieldPointIdeal (E := L) (f ∘ x)).toIdeal D') :
    D' ≤ D := by
  have hle := projectiveFieldPointIdeal_extended_le_of_source_embedding (L := L) f x
  exact curveHilbertDegree_le_of_ideal_le hle
    (curveHilbertDegree_field_extension L _ D hD) hD'

end DimensionFourDependence
