import DimensionFourDependence.CategoricalPencilCommonFactor
import DimensionFourDependence.ProjectiveSectionIntegerOrders

/-! # Integer scheme-section orders imply the original common-factor bound -/

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

/-- Bounds stated with actual integer scheme orders of the pulled-back
homogeneous sections give the original homogeneous common-factor bound.
Both divisor DVRs and the unchanged pullback orders are constructed. -/
theorem categorical_pencil_point_integer_orders_common_factor_degree
    [Module.Finite (closedGaussParameterField H I) E]
    (y : Mₑ) (hcodim : Order.coheight ((mₑ) y) = 1)
    (P : Fin 4 → R₄) (g : R₄) {c D : ℕ}
    (hg : g ≠ 0) (hgh : g.IsHomogeneous c) (hP : IsHomogMap P D)
    (hprim : IsPrimitiveVec P) (hHP : H = fun i => g * P i) (a : ℕ) :
    letI : IsIntegral Mₑ := closedGaussPencilCoefficientBaseChangeNormalization_isIntegral H I E hH e
    letI : IsNoetherian Mₑ := closedGaussPencilCoefficientBaseChangeNormalization_isNoetherian H I E hH e
    ProjectiveSourceSectionIntegerOrders (mₑ) y H a →
      ∃ Δ : R₄, Irreducible Δ ∧ Δ.IsHomogeneous Δ.totalDegree ∧
        Δ ^ a ∣ g ∧ a * Δ.totalDegree ≤ g.totalDegree ∧ a ≤ g.totalDegree := by
  let : IsIntegral Mₑ := closedGaussPencilCoefficientBaseChangeNormalization_isIntegral H I E hH e
  let : IsNoetherian Mₑ := closedGaussPencilCoefficientBaseChangeNormalization_isNoetherian H I E hH e
  intro horder
  have hcomparison := categorical_pencil_point_source_divisor_order_comparison H I E hH e y hcodim
  obtain ⟨_hS, _hA, _hDVR, hframed, _hregular⟩ := hcomparison
  obtain ⟨hDVRA, _⟩ := hframed
  let : IsDiscreteValuationRing ((Mₑ).presheaf.stalk y) := hDVRA
  let : IsIntegral Pₖ := polynomialProjective_isIntegral K
  let : IsLocallyNoetherian Pₖ := polynomialProjective_isLocallyNoetherian K
  obtain ⟨_hx, hy, _k, _hk, _horder⟩ :=
    categorical_pencil_point_source_scheme_orders H I E hH e y hcodim
  have hregularOrders := (projective_source_section_integer_orders_iff (K := K) (Y := Mₑ)
    (mₑ) y hy H a).mp horder
  exact categorical_pencil_point_source_common_factor_degree H I E hH e y hcodim
    P g hg hgh hP hprim hHP a hregularOrders

/-- At the actual generic point of a prime subvariety with dense
source-divisor image, the integer section orders give `a ≤ deg g`,
and construct an original irreducible homogeneous divisor power in `g`. -/
theorem categorical_pencil_source_divisor_integer_orders_common_factor_degree
    [Module.Finite (closedGaussParameterField H I) E]
    (Z : Set Mₑ) (hZ : IsIrreducible Z) (hZclosed : IsClosed Z)
    (D₀ : Set Pₖ) (hD : IsIrreducible D₀) (hDclosed : IsClosed D₀)
    (hdiv : Order.coheight hD.genericPoint = 1)
    (himage : closure ((mₑ) '' Z) = D₀)
    (P : Fin 4 → R₄) (g : R₄) {c D : ℕ}
    (hg : g ≠ 0) (hgh : g.IsHomogeneous c) (hP : IsHomogMap P D)
    (hprim : IsPrimitiveVec P) (hHP : H = fun i => g * P i) (a : ℕ) :
    letI : IsIntegral Mₑ := closedGaussPencilCoefficientBaseChangeNormalization_isIntegral H I E hH e
    letI : IsNoetherian Mₑ := closedGaussPencilCoefficientBaseChangeNormalization_isNoetherian H I E hH e
    ProjectiveSourceSectionIntegerOrders (mₑ) hZ.genericPoint H a →
      ∃ Δ : R₄, Irreducible Δ ∧ Δ.IsHomogeneous Δ.totalDegree ∧
        Δ ^ a ∣ g ∧ a * Δ.totalDegree ≤ g.totalDegree ∧ a ≤ g.totalDegree := by
  have hpoint := scheme_generic_point_image_eq (X := Pₖ) (Y := Mₑ) (mₑ)
    (hZ.isGenericPoint_genericPoint hZclosed) (hD.isGenericPoint_genericPoint hDclosed) himage
  have hcodim : Order.coheight ((mₑ) hZ.genericPoint) = 1 := by
    rw [hpoint]
    exact hdiv
  exact categorical_pencil_point_integer_orders_common_factor_degree H I E hH e _ hcodim
    P g hg hgh hP hprim hHP a

end DimensionFourDependence
