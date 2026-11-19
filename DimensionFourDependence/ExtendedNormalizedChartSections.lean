import DimensionFourDependence.ExtendedGaussSchemeTensorCharts
import DimensionFourDependence.TensorPencilProjectionFieldActions

/-! # Every actual normalized chart function gives its original integral coefficient

This uses sections of the structure sheaf on the actual normalization
open, rather than supplied elements of an abstract normalization ring.
The affine atlas identifies every such section with the canonical
normalization of the original tensor chart, and retains its exact
function in that chart's original fraction field.
-/

namespace DimensionFourDependence

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct

universe u

attribute [local instance] Algebra.TensorProduct.rightAlgebra

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
local notation "T₀" => S₀ ⊗[C₀] E
local notation "N₀" => normalizationRing T₀
local notation "X" => extendedClosedGaussNormalizationScheme H I E hH e
local notation "U" => extendedClosedGaussNormalizationChartOpen H I E hH e s

/-- The actual normalization chart's structure-sheaf sections are the
canonical normalization of the original tensor chart. -/
noncomputable def extendedClosedGaussNormalizedChartSectionEquiv : Γ(X, U) ≃+* N₀ :=
  ((U).topIso.symm ≪≫
    (Scheme.Γ.mapIso (extendedClosedGaussNormalizationTensorChartIso H I E hH e s).op).symm ≪≫
      Scheme.ΓSpecIso _).commRingCatIsoToRingEquiv

/-- An actual regular function on the actual normalization chart has
its original rational value in the original tensor chart's function field. -/
noncomputable def extendedClosedGaussNormalizedChartSectionValue : Γ(X, U) →+* FractionRing T₀ :=
  (algebraMap N₀ (FractionRing T₀)).comp
    (extendedClosedGaussNormalizedChartSectionEquiv H I E hH e s).toRingHom

/-- Every actual normalized chart function is integral over the entire
original tensor chart, without a separately supplied integrality proof. -/
theorem extendedClosedGaussNormalizedChartSectionValue_isIntegral (r : Γ(X, U)) :
    IsIntegral T₀ (extendedClosedGaussNormalizedChartSectionValue H I E hH e s r) :=
  (extendedClosedGaussNormalizedChartSectionEquiv H I E hH e s r).property

/-- The actual normalized chart-section realization is injective, so
nonzero regular coefficients have nonzero original rational values. -/
theorem extendedClosedGaussNormalizedChartSectionValue_injective :
    Function.Injective (extendedClosedGaussNormalizedChartSectionValue H I E hH e s) := by
  change Function.Injective (fun r =>
    ((extendedClosedGaussNormalizedChartSectionEquiv H I E hH e s r : N₀) : FractionRing T₀))
  exact Subtype.val_injective.comp
    (extendedClosedGaussNormalizedChartSectionEquiv H I E hH e s).injective

end DimensionFourDependence
