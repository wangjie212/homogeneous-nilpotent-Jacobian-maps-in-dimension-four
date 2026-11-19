import DimensionFourDependence.AffineStalkDimension
import DimensionFourDependence.GeometricRationalSourceOrders

/-! # Source codimension without a chosen affine height hypothesis -/

namespace DimensionFourDependence

open AlgebraicGeometry MvPolynomial
open scoped TensorProduct

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

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
local notation "N₀" => normalizationRing (S₀ ⊗[C₀] E)
local notation "Pₖ" => AlgebraicGeometry.Proj (homogeneousSubmodule (Fin 4) K)
local notation "mₑ" => extendedClosedGaussNormalizationSourceMorphism H I E hH e
local notation "zₑ" q:max => extendedClosedGaussNormalizationTensorChartPoint H I E hH e s q
local notation "hUₖ" => Proj.isAffineOpen_basicOpen (homogeneousSubmodule (Fin 4) K)
  (X (s.symm none)) (isHomogeneous_X (R := K) _) (by omega)

/-- The actual source stalk has dimension one exactly when its prime
has height one in the original source-coordinate affine neighborhood. -/
theorem extendedClosedGaussNormalization_source_stalk_dimension_one_iff
    (q : PrimeSpectrum N₀) :
    ringKrullDim ((Pₖ).presheaf.stalk ((mₑ) (zₑ q))) = 1 ↔
      ((hUₖ).primeIdealOf ⟨(mₑ) (zₑ q),
        extendedClosedGaussNormalizationTensorChartPoint_source_mem H I E hH e s q⟩).asIdeal.height = 1 := by
  have h := affineOpen_stalk_dimension_eq_prime_height
    (X := Pₖ) ⟨_, hUₖ⟩
    ⟨(mₑ) (zₑ q), extendedClosedGaussNormalizationTensorChartPoint_source_mem H I E hH e s q⟩
  rw [h]
  norm_cast

end DimensionFourDependence
