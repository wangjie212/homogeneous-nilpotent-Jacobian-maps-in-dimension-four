import DimensionFourDependence.NormalizationCoordinateMorphism
import DimensionFourDependence.ExtendedGaussSchemeTensorCharts

/-! # The extended pencil normalization map in the original tensor charts

The actual global normalization morphism, restricted to an original
tensor-normalization chart, is induced by the specified source inclusion
through the actual pencil affine sections.
-/

namespace DimensionFourDependence

open AlgebraicGeometry CategoryTheory
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
  (s : Fin 4 ≃ Option (Fin 3))

local notation "C₀" => closedGaussParameterField H I
local notation "S₀" => projectiveCoordinateChartAlgebra (C := C₀)
  (rationalCoordinate (K := K) (n := 4)) (s.symm none)

/-- The actual extended normalization morphism is the original tensor
ring inclusion on each of its normalized source charts. -/
theorem extendedClosedGaussNormalizationTensorChartInclusion_to_base :
    extendedClosedGaussNormalizationTensorChartInclusion H I E hH e s ≫
        extendedClosedGaussNormalizationSchemeMap H I E hH e =
      Spec.map (CommRingCat.ofHom
        ((algebraMap (S₀ ⊗[C₀] E) (normalizationRing (S₀ ⊗[C₀] E))).comp
          (extendedClosedGaussPencilTensorChartSectionEquiv H I E hH e s).toRingHom)) ≫
        (extendedClosedGaussPencilChartOpen_isAffineOpen H I E hH e s).fromSpec := by
  let : IsIntegral (extendedClosedGaussPencilScheme H I E hH e) :=
    extendedClosedGaussPencilScheme_isIntegral H I E hH e
  let : Nonempty (extendedClosedGaussPencilChartOpen H I E hH e s) :=
    extendedClosedGaussPencilChartOpen_nonempty H I E hH e s
  let b := extendedClosedGaussRatioCoordinateEquiv H I E hH e s
  let : IsDomain (S₀ ⊗[C₀] E) := Function.Injective.isDomain b b.injective
  unfold extendedClosedGaussNormalizationTensorChartInclusion
    extendedClosedGaussNormalizationTensorChartIso
    extendedClosedGaussNormalizationChartOpen
    extendedClosedGaussNormalizationSchemeMap
  have h := integralSchemeNormalizationCoordinateChart_inv_to_base
    (extendedClosedGaussPencilScheme H I E hH e)
    ⟨extendedClosedGaussPencilChartOpen H I E hH e s,
      extendedClosedGaussPencilChartOpen_isAffineOpen H I E hH e s⟩
    (S₀ ⊗[C₀] E) (extendedClosedGaussPencilTensorChartSectionEquiv H I E hH e s)
  convert! h using 1

end DimensionFourDependence
