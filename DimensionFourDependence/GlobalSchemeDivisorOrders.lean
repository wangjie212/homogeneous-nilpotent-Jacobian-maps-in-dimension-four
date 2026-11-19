import DimensionFourDependence.GlobalCurveDivisorOrders
import DimensionFourDependence.SchemeDivisorPullback
import DimensionFourDependence.PolynomialProjectiveProperties

/-! # Integer scheme orders on the actual global normalized pencil -/

namespace DimensionFourDependence

open AlgebraicGeometry MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 2000000
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

/-- At any global normalized-pencil point over a source divisor,
the actual scheme function-field pullback preserves every integer
order of vanishing. The normalized-pencil point has codimension one. -/
theorem actual_global_point_source_scheme_orders
    [Module.Finite (closedGaussParameterField H I) E]
    (y : Nₑ) (hcodim : Order.coheight ((mₑ) y) = 1) :
    letI : IsIntegral Pₖ := polynomialProjective_isIntegral K
    letI : IsLocallyNoetherian Pₖ := polynomialProjective_isLocallyNoetherian K
    letI : IsIntegral Nₑ := extendedClosedGaussNormalizationScheme_isIntegral H I E hH e
    letI : IsNoetherian Nₑ := extendedClosedGaussNormalizationScheme_isNoetherian H I E hH e
    SchemeDivisorPullbackComparison (mₑ) y := by
  let : IsIntegral Pₖ := polynomialProjective_isIntegral K
  let : IsLocallyNoetherian Pₖ := polynomialProjective_isLocallyNoetherian K
  let : IsIntegral Nₑ := extendedClosedGaussNormalizationScheme_isIntegral H I E hH e
  let : IsNoetherian Nₑ := extendedClosedGaussNormalizationScheme_isNoetherian H I E hH e
  have h := actual_global_point_source_divisor_order_comparison H I E hH e y hcodim
  exact intrinsic_divisor_pullback_scheme_orders (mₑ) y hcodim h

/-- A prime closed subvariety with dense source-divisor image has
unchanged integer orders on the schemes' actual function fields, through
the unique extension of the entire actual geometric source stalk map. -/
theorem actual_global_irreducible_source_divisor_scheme_orders
    [Module.Finite (closedGaussParameterField H I) E]
    (Z : Set Nₑ) (hZ : IsIrreducible Z) (hZclosed : IsClosed Z)
    (D₀ : Set Pₖ) (hD : IsIrreducible D₀) (hDclosed : IsClosed D₀)
    (hdiv : Order.coheight hD.genericPoint = 1)
    (himage : closure ((mₑ) '' Z) = D₀) :
    letI : IsIntegral Pₖ := polynomialProjective_isIntegral K
    letI : IsLocallyNoetherian Pₖ := polynomialProjective_isLocallyNoetherian K
    letI : IsIntegral Nₑ := extendedClosedGaussNormalizationScheme_isIntegral H I E hH e
    letI : IsNoetherian Nₑ := extendedClosedGaussNormalizationScheme_isNoetherian H I E hH e
    SchemeDivisorPullbackComparison (mₑ) hZ.genericPoint := by
  have hpoint := scheme_generic_point_image_eq (mₑ)
    (hZ.isGenericPoint_genericPoint hZclosed) (hD.isGenericPoint_genericPoint hDclosed) himage
  apply actual_global_point_source_scheme_orders H I E hH e
  rw [hpoint]
  exact hdiv

end DimensionFourDependence
