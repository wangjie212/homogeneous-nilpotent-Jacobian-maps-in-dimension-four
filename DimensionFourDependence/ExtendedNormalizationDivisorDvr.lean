import DimensionFourDependence.NormalDivisorStalkDvr
import DimensionFourDependence.ExtendedGaussPencilScheme

/-! # Every intrinsic divisor of the actual normalized extended pencil has a DVR stalk -/

namespace DimensionFourDependence

open AlgebraicGeometry

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

/-- Every actual codimension-one point supplies its own discrete
valuation stalk, independently of the dimension or image of its source
projection and without a chosen affine chart. -/
theorem extendedClosedGaussNormalization_divisor_stalk_isDVR
    (y : extendedClosedGaussNormalizationScheme H I E hH e) (hy : Order.coheight y = 1) :
    let : IsIntegral (extendedClosedGaussNormalizationScheme H I E hH e) :=
      extendedClosedGaussNormalizationScheme_isIntegral H I E hH e
    IsDiscreteValuationRing
      ((extendedClosedGaussNormalizationScheme H I E hH e).presheaf.stalk y) := by
  let X := extendedClosedGaussNormalizationScheme H I E hH e
  let : IsIntegral X := extendedClosedGaussNormalizationScheme_isIntegral H I E hH e
  let : IsNoetherian X := extendedClosedGaussNormalizationScheme_isNoetherian H I E hH e
  let : IsIntegrallyClosed (X.presheaf.stalk y) :=
    extendedClosedGaussNormalizationScheme_stalk_isIntegrallyClosed H I E hH e y
  exact normal_codimension_one_scheme_stalk_isDVR y hy

end DimensionFourDependence
