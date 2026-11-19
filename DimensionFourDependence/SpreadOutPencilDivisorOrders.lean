import DimensionFourDependence.ClosedGaussPencilSpreadScheme
import DimensionFourDependence.CategoricalPencilIntegerMultiplicity

/-! # Divisor orders from the actual spread-out pencil family

The hypothesis is density of the source image of the actual integral
family closed in the source-parameter product. The parameter model may
be arbitrary with its specified extension-field point over the original
constants. No generic-curve source density, affine prime, unramified local
model, or order comparison is assumed separately.
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
  [Module.Finite (closedGaussParameterField H I) E]
  {d : ℕ} (hH : IsHomogMap H d)
  (e : RatFunc K ≃ₐ[K] closedGaussParameterField H I)
  (model : ClosedGaussParameterSchemeModel H I E)

local notation "Pₖ" => AlgebraicGeometry.Proj (homogeneousSubmodule (Fin 4) K)
local notation "Mₑ" => closedGaussPencilCoefficientBaseChangeNormalization H I E hH e
local notation "mₑ" => closedGaussPencilCoefficientBaseChangeNormalizationSourceMorphism H I E hH e

/-- The paper's spread-out source-divisor density supplies unchanged
regular, rational and local-frame orders on the actual normalized
generic pencil through the entire actual source stalk map. -/
theorem closed_gauss_spread_out_source_divisor_order_comparison
    (Z : Set Mₑ) (hZ : IsIrreducible Z) (hZclosed : IsClosed Z)
    (D₀ : Set Pₖ) (hD : IsIrreducible D₀) (hDclosed : IsClosed D₀)
    (hdiv : Order.coheight hD.genericPoint = 1)
    (himage : closure (Set.range
      (closedGaussPencilSpreadFamilySourceMorphism H I E hH e model Z hZ)) = D₀) :
    IntrinsicDivisorPullbackComparison ((mₑ).stalkMap hZ.genericPoint).hom := by
  have hgeneric : closure ((mₑ) '' Z) = D₀ :=
    (closedGaussPencilSpreadFamilySourceMorphism_image_closure H I E hH e model Z hZ hZclosed).symm.trans himage
  exact categorical_pencil_irreducible_source_divisor_order_comparison H I E hH e
    Z hZ hZclosed D₀ hD hDclosed hdiv hgeneric

/-- The actual scheme function-field pullback preserves all integer
orders at the given generic curve point and source divisor point. -/
theorem closed_gauss_spread_out_source_divisor_scheme_orders
    (Z : Set Mₑ) (hZ : IsIrreducible Z) (hZclosed : IsClosed Z)
    (D₀ : Set Pₖ) (hD : IsIrreducible D₀) (hDclosed : IsClosed D₀)
    (hdiv : Order.coheight hD.genericPoint = 1)
    (himage : closure (Set.range
      (closedGaussPencilSpreadFamilySourceMorphism H I E hH e model Z hZ)) = D₀) :
    letI : IsIntegral Pₖ := polynomialProjective_isIntegral K
    letI : IsLocallyNoetherian Pₖ := polynomialProjective_isLocallyNoetherian K
    letI : IsIntegral Mₑ := closedGaussPencilCoefficientBaseChangeNormalization_isIntegral H I E hH e
    letI : IsNoetherian Mₑ := closedGaussPencilCoefficientBaseChangeNormalization_isNoetherian H I E hH e
    SchemeDivisorPullbackComparison (mₑ) hZ.genericPoint := by
  have hgeneric : closure ((mₑ) '' Z) = D₀ :=
    (closedGaussPencilSpreadFamilySourceMorphism_image_closure H I E hH e model Z hZ hZclosed).symm.trans himage
  exact categorical_pencil_irreducible_source_divisor_scheme_orders H I E hH e
    Z hZ hZclosed D₀ hD hDclosed hdiv hgeneric

/-- Orders of the original homogeneous sections along the prime curve,
stated as actual integer scheme orders, give the original homogeneous
divisor-power and common-factor degree conclusions under the paper's
actual spread-out source-image hypothesis. -/
theorem closed_gauss_spread_out_section_orders_common_factor_degree
    (Z : Set Mₑ) (hZ : IsIrreducible Z) (hZclosed : IsClosed Z)
    (D₀ : Set Pₖ) (hD : IsIrreducible D₀) (hDclosed : IsClosed D₀)
    (hdiv : Order.coheight hD.genericPoint = 1)
    (himage : closure (Set.range
      (closedGaussPencilSpreadFamilySourceMorphism H I E hH e model Z hZ)) = D₀)
    (P : Fin 4 → MvPolynomial (Fin 4) K) (g : MvPolynomial (Fin 4) K) {c D : ℕ}
    (hg : g ≠ 0) (hgh : g.IsHomogeneous c) (hP : IsHomogMap P D)
    (hprim : IsPrimitiveVec P) (hHP : H = fun i => g * P i) (a : ℕ) :
    letI : IsIntegral Mₑ := closedGaussPencilCoefficientBaseChangeNormalization_isIntegral H I E hH e
    letI : IsNoetherian Mₑ := closedGaussPencilCoefficientBaseChangeNormalization_isNoetherian H I E hH e
    ProjectiveSourceSectionIntegerOrders (mₑ) hZ.genericPoint H a →
      ∃ Δ : MvPolynomial (Fin 4) K, Irreducible Δ ∧ Δ.IsHomogeneous Δ.totalDegree ∧
        Δ ^ a ∣ g ∧ a * Δ.totalDegree ≤ g.totalDegree ∧ a ≤ g.totalDegree := by
  have hgeneric : closure ((mₑ) '' Z) = D₀ :=
    (closedGaussPencilSpreadFamilySourceMorphism_image_closure H I E hH e model Z hZ hZclosed).symm.trans himage
  exact categorical_pencil_source_divisor_integer_orders_common_factor_degree H I E hH e
    Z hZ hZclosed D₀ hD hDclosed hdiv hgeneric P g hg hgh hP hprim hHP a

end DimensionFourDependence
