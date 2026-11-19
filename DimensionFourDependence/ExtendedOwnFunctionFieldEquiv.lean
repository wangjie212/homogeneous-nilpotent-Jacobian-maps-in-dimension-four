import DimensionFourDependence.ExtendedOwnCoordinateCharts

/-! # The original chart field and own scheme field agree over the actual coefficients -/

namespace DimensionFourDependence

open AlgebraicGeometry
open scoped TensorProduct

attribute [local instance] Algebra.TensorProduct.rightAlgebra

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
local notation "T₀" => projectiveCoordinateChartAlgebra (C := C₀)
  (rationalCoordinate (K := K) (n := 4)) (s.symm none) ⊗[C₀] E
local notation "N" => extendedClosedGaussNormalizationScheme H I E hH e
local notation "w" => extendedClosedGaussNormalizationHyperplaneWeight H I E hH e

local instance extendedOwnFunctionFieldEquivIntegral : IsIntegral N := extendedClosedGaussNormalizationScheme_isIntegral H I E hH e
local instance extendedOwnFunctionFieldEquivDomain : IsDomain T₀ := original_tensor_pencil_chart_isDomain H I E s
noncomputable local instance extendedOwnFunctionFieldEquivAlgebra : Algebra E (N).functionField :=
  extendedClosedGaussOwnFunctionFieldAlgebra H I E hH e

/-- The actual original chart fraction field and own scheme field
are identified over the actual extended coefficient field. -/
noncomputable def extendedClosedGaussNormalizedChartFunctionFieldAlgEquiv :
    FractionRing T₀ ≃ₐ[E] (N).functionField :=
  { extendedClosedGaussNormalizedChartFunctionFieldEquiv H I E hH e s with
    commutes' := fun c =>
      (congrArg (extendedClosedGaussNormalizedChartFunctionFieldEquiv H I E hH e s)
        (IsScalarTower.algebraMap_apply E T₀ (FractionRing T₀) c)).trans
          (extendedClosedGaussTensorChartToOwnFunctionField_coefficient H I E hH e s c) }

/-- The coefficient-field identification retains the original three
tensor coordinates as exactly the native original-frame ratios. -/
theorem extendedClosedGaussNormalizedChartFunctionFieldAlgEquiv_coordinate (i : Fin 3) :
    extendedClosedGaussNormalizedChartFunctionFieldAlgEquiv H I E hH e s
        (algebraMap T₀ (FractionRing T₀) (originalTensorPencilCoordinate H I E s i)) =
      w (s.symm (some i)) / w (s.symm none) :=
  extendedClosedGaussTensorChartToOwnFunctionField_original_coordinate H I E hH e s i

/-- The inverse actual field identification sends every native
original coordinate ratio to its original tensor fraction value. -/
theorem extendedClosedGaussNormalizedChartFunctionFieldAlgEquiv_symm_coordinate (i : Fin 3) :
    (extendedClosedGaussNormalizedChartFunctionFieldAlgEquiv H I E hH e s).symm
        (w (s.symm (some i)) / w (s.symm none)) =
      algebraMap T₀ (FractionRing T₀) (originalTensorPencilCoordinate H I E s i) := by
  apply (extendedClosedGaussNormalizedChartFunctionFieldAlgEquiv H I E hH e s).injective
  rw [AlgEquiv.apply_symm_apply, extendedClosedGaussNormalizedChartFunctionFieldAlgEquiv_coordinate]

end DimensionFourDependence
