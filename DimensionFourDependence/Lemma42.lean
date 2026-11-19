import DimensionFourDependence.SpreadOutPencilDivisorOrders
import DimensionFourDependence.SchemeFramedDivisorPullback

/-! # Lemma 4.2: spread-out divisor orders and the common-factor bound

The normalized generic pencil is the intrinsic normalization of the
actual categorical coefficient base change. A prime curve is spread
by its actual reduced integral closure in the source-parameter product.
The parameter model can be any curve with the specified extension-field
point over the original constants. The source-divisor image condition
is imposed on this spread-out family, as in the paper.

Rational sections are expressed by their actual function-field
coefficients in a regular local frame at the source divisor. The single
constructed pullback preserves their integer orders and every regular
frame transition. The homogeneous-section corollary uses actual integer
scheme orders, with zero sections handled explicitly.
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

/-- Lemma 4.2's rational-section assertion: the actual field pullback
extends the entire geometric source stalk, preserves orders along the
specified source divisor, and preserves the coefficient order in every
regular local frame. The original prime curve point is retained. -/
theorem lemma_4_2_rational_section_orders
    (Z : Set Mₑ) (hZ : IsIrreducible Z) (hZclosed : IsClosed Z)
    (D₀ : Set Pₖ) (hD : IsIrreducible D₀) (hDclosed : IsClosed D₀)
    (hdiv : Order.coheight hD.genericPoint = 1)
    (himage : closure (Set.range
      (closedGaussPencilSpreadFamilySourceMorphism H I E hH e model Z hZ)) = D₀) :
    letI : IsIntegral Pₖ := polynomialProjective_isIntegral K
    letI : IsLocallyNoetherian Pₖ := polynomialProjective_isLocallyNoetherian K
    letI : IsIntegral Mₑ := closedGaussPencilCoefficientBaseChangeNormalization_isIntegral H I E hH e
    letI : IsNoetherian Mₑ := closedGaussPencilCoefficientBaseChangeNormalization_isNoetherian H I E hH e
    (mₑ) hZ.genericPoint = hD.genericPoint ∧
      Order.coheight hZ.genericPoint = 1 ∧
        ∃ j : (Pₖ).functionField →+* (Mₑ).functionField,
          (∀ z : (Pₖ).presheaf.stalk ((mₑ) hZ.genericPoint),
            j (algebraMap ((Pₖ).presheaf.stalk ((mₑ) hZ.genericPoint)) (Pₖ).functionField z) =
              algebraMap ((Mₑ).presheaf.stalk hZ.genericPoint) (Mₑ).functionField
                ((mₑ).stalkMap hZ.genericPoint z)) ∧
          (∀ x : (Pₖ).functionField, (Pₖ).ord x hD.genericPoint =
            (Mₑ).ord (j x) hZ.genericPoint) ∧
          ∀ (v : ((Pₖ).presheaf.stalk ((mₑ) hZ.genericPoint))ˣ) (x : (Pₖ).functionField),
            (Mₑ).ord (j (algebraMap ((Pₖ).presheaf.stalk ((mₑ) hZ.genericPoint))
              (Pₖ).functionField (v : (Pₖ).presheaf.stalk ((mₑ) hZ.genericPoint)) * x)) hZ.genericPoint =
                (Pₖ).ord x hD.genericPoint := by
  let : IsIntegral Pₖ := polynomialProjective_isIntegral K
  let : IsLocallyNoetherian Pₖ := polynomialProjective_isLocallyNoetherian K
  let : IsIntegral Mₑ := closedGaussPencilCoefficientBaseChangeNormalization_isIntegral H I E hH e
  let : IsNoetherian Mₑ := closedGaussPencilCoefficientBaseChangeNormalization_isNoetherian H I E hH e
  have hgeneric : closure ((mₑ) '' Z) = D₀ :=
    (closedGaussPencilSpreadFamilySourceMorphism_image_closure H I E hH e model Z hZ hZclosed).symm.trans himage
  have hpoint := scheme_generic_point_image_eq (X := Pₖ) (Y := Mₑ) (mₑ)
    (hZ.isGenericPoint_genericPoint hZclosed) (hD.isGenericPoint_genericPoint hDclosed) hgeneric
  have horders := closed_gauss_spread_out_source_divisor_scheme_orders H I E hH e model
    Z hZ hZclosed D₀ hD hDclosed hdiv himage
  obtain ⟨_hx, hy, j, hj, horder, hframes⟩ :=
    scheme_divisor_pullback_all_regular_frames (X := Pₖ) (Y := Mₑ) (mₑ) hZ.genericPoint horders
  refine ⟨hpoint, hy, j, hj, ?_, ?_⟩
  · intro x
    rw [← hpoint]
    exact horder x
  · intro v x
    rw [← hpoint]
    exact hframes v x

/-- Lemma 4.2's common-factor conclusion: order at least a of every
original homogeneous component along the prime curve forces `deg g ≥ a`.
The proof also constructs a homogeneous irreducible divisor power in g. -/
theorem lemma_4_2_common_factor_degree
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
        Δ ^ a ∣ g ∧ a * Δ.totalDegree ≤ g.totalDegree ∧ a ≤ g.totalDegree :=
  closed_gauss_spread_out_section_orders_common_factor_degree H I E hH e model
    Z hZ hZclosed D₀ hD hDclosed hdiv himage P g hg hgh hP hprim hHP a

end DimensionFourDependence
