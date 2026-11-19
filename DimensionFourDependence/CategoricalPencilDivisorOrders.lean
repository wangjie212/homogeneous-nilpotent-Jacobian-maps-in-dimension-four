import DimensionFourDependence.ClosedGaussPencilBaseChangeNormalizationProperties
import DimensionFourDependence.SchemeDivisorPullbackIso
import DimensionFourDependence.GlobalSchemeDivisorOrders

/-! # Source divisor orders on the intrinsic categorical normalization

The normalization is formed from the actual categorical coefficient
pullback, in its own function field. Its actual map to the original
projective source preserves divisor orders at every point over a divisor.
-/

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
local notation "Mₑ" => closedGaussPencilCoefficientBaseChangeNormalization H I E hH e
local notation "mₑ" => closedGaussPencilCoefficientBaseChangeNormalizationSourceMorphism H I E hH e

/-- The entire actual stalk pullback on the categorical normalization
preserves regular, rational, and local-frame divisor orders. -/
theorem categorical_pencil_point_source_divisor_order_comparison
    [Module.Finite (closedGaussParameterField H I) E]
    (y : Mₑ) (hcodim : Order.coheight ((mₑ) y) = 1) :
    IntrinsicDivisorPullbackComparison ((mₑ).stalkMap y).hom := by
  exact intrinsic_divisor_pullback_iso (X := Pₖ) (Y := Nₑ) (Z := Mₑ)
    (extendedClosedGaussNormalizationCoefficientBaseChangeIso H I E hH e)
    (extendedClosedGaussNormalizationSourceMorphism H I E hH e) (mₑ)
    (extendedClosedGaussNormalizationCoefficientBaseChangeIso_source H I E hH e)
    (actual_global_point_source_divisor_order_comparison H I E hH e) y hcodim

/-- Integer orders in the actual scheme function fields agree, and
the upstairs point is itself of codimension one. -/
theorem categorical_pencil_point_source_scheme_orders
    [Module.Finite (closedGaussParameterField H I) E]
    (y : Mₑ) (hcodim : Order.coheight ((mₑ) y) = 1) :
    letI : IsIntegral Pₖ := polynomialProjective_isIntegral K
    letI : IsLocallyNoetherian Pₖ := polynomialProjective_isLocallyNoetherian K
    letI : IsIntegral Mₑ := closedGaussPencilCoefficientBaseChangeNormalization_isIntegral H I E hH e
    letI : IsNoetherian Mₑ := closedGaussPencilCoefficientBaseChangeNormalization_isNoetherian H I E hH e
    SchemeDivisorPullbackComparison (mₑ) y := by
  let : IsIntegral Pₖ := polynomialProjective_isIntegral K
  let : IsLocallyNoetherian Pₖ := polynomialProjective_isLocallyNoetherian K
  let : IsIntegral Mₑ := closedGaussPencilCoefficientBaseChangeNormalization_isIntegral H I E hH e
  let : IsNoetherian Mₑ := closedGaussPencilCoefficientBaseChangeNormalization_isNoetherian H I E hH e
  exact intrinsic_divisor_pullback_scheme_orders (X := Pₖ) (Y := Mₑ) (mₑ) y hcodim
    (categorical_pencil_point_source_divisor_order_comparison H I E hH e y hcodim)

/-- A prime closed subvariety with dense source-divisor image has the
intrinsic comparison, without choosing an affine prime or local model. -/
theorem categorical_pencil_irreducible_source_divisor_order_comparison
    [Module.Finite (closedGaussParameterField H I) E]
    (Z : Set Mₑ) (hZ : IsIrreducible Z) (hZclosed : IsClosed Z)
    (D₀ : Set Pₖ) (hD : IsIrreducible D₀) (hDclosed : IsClosed D₀)
    (hdiv : Order.coheight hD.genericPoint = 1)
    (himage : closure ((mₑ) '' Z) = D₀) :
    IntrinsicDivisorPullbackComparison ((mₑ).stalkMap hZ.genericPoint).hom := by
  have hpoint := scheme_generic_point_image_eq (X := Pₖ) (Y := Mₑ) (mₑ)
    (hZ.isGenericPoint_genericPoint hZclosed) (hD.isGenericPoint_genericPoint hDclosed) himage
  apply categorical_pencil_point_source_divisor_order_comparison H I E hH e
  rw [hpoint]
  exact hdiv

/-- The actual scheme-function-field comparison holds at the generic
point of every such prime subvariety on the categorical normalization. -/
theorem categorical_pencil_irreducible_source_divisor_scheme_orders
    [Module.Finite (closedGaussParameterField H I) E]
    (Z : Set Mₑ) (hZ : IsIrreducible Z) (hZclosed : IsClosed Z)
    (D₀ : Set Pₖ) (hD : IsIrreducible D₀) (hDclosed : IsClosed D₀)
    (hdiv : Order.coheight hD.genericPoint = 1)
    (himage : closure ((mₑ) '' Z) = D₀) :
    letI : IsIntegral Pₖ := polynomialProjective_isIntegral K
    letI : IsLocallyNoetherian Pₖ := polynomialProjective_isLocallyNoetherian K
    letI : IsIntegral Mₑ := closedGaussPencilCoefficientBaseChangeNormalization_isIntegral H I E hH e
    letI : IsNoetherian Mₑ := closedGaussPencilCoefficientBaseChangeNormalization_isNoetherian H I E hH e
    SchemeDivisorPullbackComparison (mₑ) hZ.genericPoint := by
  have hpoint := scheme_generic_point_image_eq (X := Pₖ) (Y := Mₑ) (mₑ)
    (hZ.isGenericPoint_genericPoint hZclosed) (hD.isGenericPoint_genericPoint hDclosed) himage
  apply categorical_pencil_point_source_scheme_orders H I E hH e
  rw [hpoint]
  exact hdiv

end DimensionFourDependence
