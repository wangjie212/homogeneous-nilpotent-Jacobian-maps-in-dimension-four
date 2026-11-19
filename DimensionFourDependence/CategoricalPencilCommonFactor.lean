import DimensionFourDependence.CategoricalPencilDivisorOrders
import DimensionFourDependence.ProjectiveSectionOrderMultiplicity

/-! # Orders and common-factor degree on the categorical normalized pencil

For a prime subvariety with dense source-divisor image, the actual
geometric section orders force a homogeneous divisor power into the
original common factor. The normalization is the intrinsic normalization
of the actual categorical coefficient base change.
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
local notation "R₄" => MvPolynomial (Fin 4) K
local notation "Mₑ" => closedGaussPencilCoefficientBaseChangeNormalization H I E hH e
local notation "mₑ" => closedGaussPencilCoefficientBaseChangeNormalizationSourceMorphism H I E hH e

/-- Every point over a source divisor satisfies the common-factor
conclusion from orders of the actual pulled-back homogeneous sections. -/
theorem categorical_pencil_point_source_common_factor_degree
    [Module.Finite (closedGaussParameterField H I) E]
    (y : Mₑ) (hcodim : Order.coheight ((mₑ) y) = 1)
    (P : Fin 4 → R₄) (g : R₄) {c D : ℕ}
    (hg : g ≠ 0) (hgh : g.IsHomogeneous c) (hP : IsHomogMap P D)
    (hprim : IsPrimitiveVec P) (hHP : H = fun i => g * P i)
    (a : ℕ) (horder : ProjectiveSourceSectionOrders (mₑ) y H a) :
    ∃ Δ : R₄, Irreducible Δ ∧ Δ.IsHomogeneous Δ.totalDegree ∧
      Δ ^ a ∣ g ∧ a * Δ.totalDegree ≤ g.totalDegree ∧ a ≤ g.totalDegree := by
  exact geometric_projective_section_orders_common_factor_degree (K := K) (Y := Mₑ) (mₑ) y
    hcodim (categorical_pencil_point_source_divisor_order_comparison H I E hH e y hcodim)
    H P g hg hgh hP hprim hHP a horder

/-- A prime subvariety with dense source-divisor image has both the
intrinsic order comparison and the common-factor degree conclusion.
All orders use its actual generic-point stalk and actual source map. -/
theorem categorical_pencil_source_divisor_orders_common_factor_degree
    [Module.Finite (closedGaussParameterField H I) E]
    (Z : Set Mₑ) (hZ : IsIrreducible Z) (hZclosed : IsClosed Z)
    (D₀ : Set Pₖ) (hD : IsIrreducible D₀) (hDclosed : IsClosed D₀)
    (hdiv : Order.coheight hD.genericPoint = 1)
    (himage : closure ((mₑ) '' Z) = D₀)
    (P : Fin 4 → R₄) (g : R₄) {c D : ℕ}
    (hg : g ≠ 0) (hgh : g.IsHomogeneous c) (hP : IsHomogMap P D)
    (hprim : IsPrimitiveVec P) (hHP : H = fun i => g * P i)
    (a : ℕ) (horder : ProjectiveSourceSectionOrders (mₑ) hZ.genericPoint H a) :
    IntrinsicDivisorPullbackComparison ((mₑ).stalkMap hZ.genericPoint).hom ∧
      ∃ Δ : R₄, Irreducible Δ ∧ Δ.IsHomogeneous Δ.totalDegree ∧
        Δ ^ a ∣ g ∧ a * Δ.totalDegree ≤ g.totalDegree ∧ a ≤ g.totalDegree := by
  have hpoint := scheme_generic_point_image_eq (X := Pₖ) (Y := Mₑ) (mₑ)
    (hZ.isGenericPoint_genericPoint hZclosed) (hD.isGenericPoint_genericPoint hDclosed) himage
  have hcodim : Order.coheight ((mₑ) hZ.genericPoint) = 1 := by
    rw [hpoint]
    exact hdiv
  exact ⟨categorical_pencil_point_source_divisor_order_comparison H I E hH e _ hcodim,
    categorical_pencil_point_source_common_factor_degree H I E hH e _ hcodim
      P g hg hgh hP hprim hHP a horder⟩

end DimensionFourDependence
