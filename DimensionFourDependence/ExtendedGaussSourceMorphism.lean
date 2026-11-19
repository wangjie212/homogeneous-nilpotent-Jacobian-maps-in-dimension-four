import DimensionFourDependence.ProjectiveCoefficientMorphism
import DimensionFourDependence.ExtendedGaussSchemeTensorCharts

/-! # The global extended pencil maps to the original projective source

The original coefficient map, the actual extended projective closed
immersion, and normalization define the geometric source projection.
Its coordinate inverse opens are precisely the existing original tensor
charts on the extended pencil and its normalization.
-/

namespace DimensionFourDependence

open AlgebraicGeometry CategoryTheory MvPolynomial
open scoped TensorProduct

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

variable {K : Type u} [Field K] [CharZero K]
  (H : Fin 4 → MvPolynomial (Fin 4) K) (I : ImageRelationWitness H)
  (E : Type u) [Field E] [Algebra (closedGaussParameterField H I) E]
  [Algebra.IsAlgebraic (closedGaussParameterField H I) E]
  {d : ℕ} (hH : IsHomogMap H d)
  (e : RatFunc K ≃ₐ[K] closedGaussParameterField H I)

/-- The original source coefficients enter the extended pencil through
the actual closed Gauss parameter field. -/
noncomputable def extendedClosedGaussSourceCoefficientHom : K →+* E :=
  (algebraMap (closedGaussParameterField H I) E).comp
    (algebraMap K (closedGaussParameterField H I))

/-- The actual projective extended pencil projects to the original
projective source through its original four homogeneous coordinates. -/
noncomputable def extendedClosedGaussPencilSourceMorphism :
    extendedClosedGaussPencilScheme H I E hH e ⟶
      AlgebraicGeometry.Proj (homogeneousSubmodule (Fin 4) K) :=
  extendedClosedGaussPencilSchemeInclusion H I E hH e ≫
    polynomialProjectiveCoefficientMap (extendedClosedGaussSourceCoefficientHom H I E)

/-- The normalization formed after coefficient extension maps to the
original projective source by the actual global scheme morphism. -/
noncomputable def extendedClosedGaussNormalizationSourceMorphism :
    extendedClosedGaussNormalizationScheme H I E hH e ⟶
      AlgebraicGeometry.Proj (homogeneousSubmodule (Fin 4) K) :=
  extendedClosedGaussNormalizationSchemeMap H I E hH e ≫
    extendedClosedGaussPencilSourceMorphism H I E hH e

/-- The original projective coordinate open pulls back to the existing
tensor coordinate chart of the actual extended pencil scheme. -/
theorem extendedClosedGaussPencilSourceMorphism_preimage_basicOpen
    (s : Fin 4 ≃ Option (Fin 3)) :
    extendedClosedGaussPencilSourceMorphism H I E hH e ⁻¹ᵁ
        Proj.basicOpen (homogeneousSubmodule (Fin 4) K) (X (s.symm none)) =
      extendedClosedGaussPencilChartOpen H I E hH e s := by
  unfold extendedClosedGaussPencilSourceMorphism
  rw [Scheme.Hom.comp_preimage, polynomialProjectiveCoefficientMap_preimage_basicOpen]
  rfl

/-- The same original source-coordinate open pulls back on the actual
global normalization to its existing tensor-normalization chart. -/
theorem extendedClosedGaussNormalizationSourceMorphism_preimage_basicOpen
    (s : Fin 4 ≃ Option (Fin 3)) :
    extendedClosedGaussNormalizationSourceMorphism H I E hH e ⁻¹ᵁ
        Proj.basicOpen (homogeneousSubmodule (Fin 4) K) (X (s.symm none)) =
      extendedClosedGaussNormalizationChartOpen H I E hH e s := by
  unfold extendedClosedGaussNormalizationSourceMorphism
  rw [Scheme.Hom.comp_preimage, extendedClosedGaussPencilSourceMorphism_preimage_basicOpen]
  rfl

/-- Every original tensor-normalization prime gives a global point
whose actual source image lies in its original projective coordinate chart. -/
theorem extendedClosedGaussNormalizationTensorChartPoint_source_mem
    (s : Fin 4 ≃ Option (Fin 3))
    (q : PrimeSpectrum (normalizationRing
      (projectiveCoordinateChartAlgebra (C := closedGaussParameterField H I)
        (rationalCoordinate (K := K) (n := 4)) (s.symm none) ⊗[closedGaussParameterField H I] E))) :
    extendedClosedGaussNormalizationSourceMorphism H I E hH e
        (extendedClosedGaussNormalizationTensorChartPoint H I E hH e s q) ∈
      Proj.basicOpen (homogeneousSubmodule (Fin 4) K) (X (s.symm none)) := by
  change extendedClosedGaussNormalizationTensorChartPoint H I E hH e s q ∈
    extendedClosedGaussNormalizationSourceMorphism H I E hH e ⁻¹ᵁ
      Proj.basicOpen (homogeneousSubmodule (Fin 4) K) (X (s.symm none))
  rw [extendedClosedGaussNormalizationSourceMorphism_preimage_basicOpen]
  unfold extendedClosedGaussNormalizationTensorChartPoint
    extendedClosedGaussNormalizationTensorChartInclusion
  exact (extendedClosedGaussNormalizationTensorChartIso H I E hH e s).inv q |>.property

end DimensionFourDependence
