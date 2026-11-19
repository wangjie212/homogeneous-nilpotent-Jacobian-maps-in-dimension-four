import DimensionFourDependence.ExtendedGaussSchemeTensorAtlas
import DimensionFourDependence.ExtendedGaussNormalizationStalkMaps

/-! # Every global normalized point comes from an original tensor prime -/

namespace DimensionFourDependence

open AlgebraicGeometry MvPolynomial
open scoped TensorProduct

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

/-- No global point is omitted by the original tensor-normalization
prime models. The representation is constructed from the actual affine cover. -/
theorem extendedClosedGaussNormalizationPoint_exists_tensor_prime
    (y : extendedClosedGaussNormalizationScheme H I E hH e) :
    ∃ (a : Fin 4) (q : PrimeSpectrum (normalizationRing
      (projectiveCoordinateChartAlgebra (C := closedGaussParameterField H I)
        (rationalCoordinate (K := K) (n := 4)) ((finSuccEquiv' a).symm none) ⊗[closedGaussParameterField H I] E))),
      extendedClosedGaussNormalizationTensorChartPoint H I E hH e (finSuccEquiv' a) q = y := by
  let 𝒰 := extendedClosedGaussNormalizationTensorAffineCover H I E hH e
  obtain ⟨q, hq⟩ := 𝒰.covers y
  refine ⟨𝒰.idx y, ?_⟩
  refine ⟨q, ?_⟩
  unfold extendedClosedGaussNormalizationTensorChartPoint
  exact hq

end DimensionFourDependence
