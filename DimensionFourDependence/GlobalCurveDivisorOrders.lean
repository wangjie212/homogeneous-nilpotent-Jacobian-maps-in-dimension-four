import DimensionFourDependence.GlobalPointDivisorOrders
import DimensionFourDependence.GlobalDivisorImagePrime

/-! # Prime subvarieties with dense source-divisor image

An irreducible closed subset of the actual global normalization has a
generic point. Density of its actual source image in a divisor identifies
that point's image with the divisor's generic point. The global order
comparison therefore applies without an assumed affine contraction.
-/

namespace DimensionFourDependence

open AlgebraicGeometry MvPolynomial

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

local notation "Pₖ" => AlgebraicGeometry.Proj (homogeneousSubmodule (Fin 4) K)
local notation "Nₑ" => extendedClosedGaussNormalizationScheme H I E hH e
local notation "mₑ" => extendedClosedGaussNormalizationSourceMorphism H I E hH e

/-- A prime closed subvariety of the actual normalization whose source
image is dense in a source divisor has the intrinsic regular, rational
and compatible-frame order comparison at its generic point. -/
theorem actual_global_irreducible_source_divisor_order_comparison
    [Module.Finite (closedGaussParameterField H I) E]
    (Z : Set Nₑ) (hZ : IsIrreducible Z) (hZclosed : IsClosed Z)
    (D₀ : Set Pₖ) (hD : IsIrreducible D₀) (hDclosed : IsClosed D₀)
    (hdiv : Order.coheight hD.genericPoint = 1)
    (himage : closure ((mₑ) '' Z) = D₀) :
    IntrinsicDivisorPullbackComparison ((mₑ).stalkMap hZ.genericPoint).hom := by
  have hpoint := scheme_generic_point_image_eq (mₑ)
    (hZ.isGenericPoint_genericPoint hZclosed) (hD.isGenericPoint_genericPoint hDclosed) himage
  apply actual_global_point_source_divisor_order_comparison H I E hH e
  rw [hpoint]
  exact hdiv

end DimensionFourDependence
