import DimensionFourDependence.ExtendedNativeSourceFormPullbacks
import DimensionFourDependence.ExtendedOutputSpanMultiplicity
import DimensionFourDependence.GlobalSchemeDivisorOrders

/-! # The actual source-divisor multiplicity contradiction after (4.5) -/

namespace DimensionFourDependence

open MvPolynomial AlgebraicGeometry

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

variable {K : Type u} [Field K] [CharZero K]
  (H : Fin 4 → MvPolynomial (Fin 4) K) (I : ImageRelationWitness H)
  (E : Type u) [Field E] [Algebra (closedGaussParameterField H I) E]
  [Algebra.IsAlgebraic (closedGaussParameterField H I) E]
  [Module.Finite (closedGaussParameterField H I) E]
  {d : ℕ} (hH : IsHomogMap H d)
  (e : RatFunc K ≃ₐ[K] closedGaussParameterField H I)

local notation "N" => extendedClosedGaussNormalizationScheme H I E hH e
local notation "V" a:max => extendedClosedGaussNormalizationChartOpen H I E hH e (finSuccEquiv' a)
local notation "w" => extendedClosedGaussNormalizationHyperplaneWeight H I E hH e
local notation "m" => extendedClosedGaussNormalizationSourceMorphism H I E hH e
local notation "P₀" => AlgebraicGeometry.Proj (homogeneousSubmodule (Fin 4) K)

local instance nativePencilCommonFactorContradictionIntegral : IsIntegral N :=
  extendedClosedGaussNormalizationScheme_isIntegral H I E hH e
local instance nativePencilCommonFactorContradictionNoetherian : IsNoetherian N :=
  extendedClosedGaussNormalizationScheme_isNoetherian H I E hH e
noncomputable local instance nativePencilCommonFactorContradictionAlgebra : Algebra E (N).functionField :=
  extendedClosedGaussOwnFunctionFieldAlgebra H I E hH e

/-- Actual native component-coefficient orders over an original
source divisor imply the original homogeneous common-factor bound.
Their identification with actual source stalk pullbacks is derived. -/
theorem actual_native_component_orders_common_factor_degree
    (z : N) (hcodim : Order.coheight ((m) z) = 1) (a : Fin 4) (ha : z ∈ V a)
    (P : Fin 4 → MvPolynomial (Fin 4) K) (g : MvPolynomial (Fin 4) K) {c fdeg : ℕ}
    (hg : g ≠ 0) (hgh : g.IsHomogeneous c) (hP : IsHomogMap P fdeg)
    (hprim : IsPrimitiveVec P) (hHP : H = fun i => g * P i) (b : ℕ)
    (horder : ∀ i, extendedClosedGaussPolynomialCoefficientGerm H I E hH e
      (MvPolynomial.map (extendedClosedGaussSourceCoefficientHom H I E) (H i)) z a ha ∈
        IsLocalRing.maximalIdeal ((N).presheaf.stalk z) ^ b) :
    ∃ Δ : MvPolynomial (Fin 4) K, Irreducible Δ ∧ Δ.IsHomogeneous Δ.totalDegree ∧
      Δ ^ b ∣ g ∧ b * Δ.totalDegree ≤ g.totalDegree ∧ b ≤ g.totalDegree := by
  exact geometric_projective_section_orders_common_factor_degree m z hcodim
    (actual_global_point_source_divisor_order_comparison H I E hH e z hcodim)
    H P g hg hgh hP hprim hHP b
    (actual_native_component_germ_orders_supply_source_section_orders H I E hH e z a ha b horder)

variable (hGauss : gaussImageDimension H I = 1)
  (p q : MvPolynomial (Fin 4) K) {D : ℕ}
  (hq0 : q ≠ 0) (hrel : IsRelPrime p q) (hpH : p.IsHomogeneous D) (hqH : q.IsHomogeneous D)
  (ht : closedGaussParameterSourceHom H I e RatFunc.X =
    algebraMap _ (FractionRing (MvPolynomial (Fin 4) K)) p /
      algebraMap _ (FractionRing (MvPolynomial (Fin 4) K)) q)

include hGauss hq0 hrel hpH hqH ht in
/-- The original rational root and product-power equations plus the
ruling-span relation yield a divisor power in the original common factor
at any vanishing point of the actual section U over a source divisor.
All source-component order hypotheses are constructed internally. -/
theorem actual_native_pencil_output_span_common_factor_degree
    (ν cS cN : Fin 4 → E) (r : (N).functionField) (hr : r ≠ 0) (hd : 0 < d)
    (hroot : r ^ d = aeval w (extendedClosedGaussOutputLinearPolynomial H I E cS))
    (α β : E)
    (hprod : (algebraMap E (N).functionField α * (∑ i, algebraMap E (N).functionField (ν i) * w i) +
        algebraMap E (N).functionField β * r) *
          aeval w (extendedClosedGaussOutputLinearPolynomial H I E cN) = r ^ (d + 1))
    (bS bN : Fin 4 → E)
    (hspan : ∀ i, aeval w (MvPolynomial.map (extendedClosedGaussSourceCoefficientHom H I E) (H i)) =
      algebraMap E (N).functionField (bS i) * aeval w (extendedClosedGaussOutputLinearPolynomial H I E cS) +
        algebraMap E (N).functionField (bN i) * aeval w (extendedClosedGaussOutputLinearPolynomial H I E cN))
    (z : N) (hcodim : Order.coheight ((m) z) = 1) (a : Fin 4) (ha : z ∈ V a)
    (hvan : (N).presheaf.germ (V a) z ha
        (extendedClosedGaussHyperplaneGlobalCoefficient H I E hH e
          (extendedClosedGaussRootCombinationSection H I E hH e ν cS r hd hroot α β) a) ∈
      IsLocalRing.maximalIdeal ((N).presheaf.stalk z))
    (P : Fin 4 → MvPolynomial (Fin 4) K) (g : MvPolynomial (Fin 4) K) {c fdeg : ℕ}
    (hg : g ≠ 0) (hgh : g.IsHomogeneous c) (hP : IsHomogMap P fdeg)
    (hprim : IsPrimitiveVec P) (hHP : H = fun i => g * P i) :
    1 ≤ D ∧ ∃ Δ : MvPolynomial (Fin 4) K, Irreducible Δ ∧ Δ.IsHomogeneous Δ.totalDegree ∧
      Δ ^ (d + 1 - D) ∣ g ∧ (d + 1 - D) * Δ.totalDegree ≤ g.totalDegree ∧
        d + 1 - D ≤ g.totalDegree := by
  let : IsIntegral P₀ := polynomialProjective_isIntegral K
  let : IsLocallyNoetherian P₀ := polynomialProjective_isLocallyNoetherian K
  obtain ⟨_hx, hz, _⟩ := actual_global_point_source_scheme_orders H I E hH e z hcodim
  obtain ⟨hD, horder⟩ := actual_native_pencil_output_span_common_multiplicity H I E hH e hGauss
    p q hq0 hrel hpH hqH ht ν cS cN r hr hd hroot α β hprod bS bN hspan z hz a ha hvan
  exact ⟨hD, actual_native_component_orders_common_factor_degree H I E hH e z hcodim a ha
    P g hg hgh hP hprim hHP (d + 1 - D) horder⟩

include hGauss hq0 hrel hpH hqH ht in
/-- The nonproportional-ruling product-power configuration is
impossible at a zero of U over an original source divisor when the
original pencil-degree bound D <= d-deg(g) holds. The common-factor
lower bound and the contradiction are both derived. -/
theorem no_actual_native_pencil_output_span_product_power_source_divisor
    (ν cS cN : Fin 4 → E) (r : (N).functionField) (hr : r ≠ 0) (hd : 0 < d)
    (hroot : r ^ d = aeval w (extendedClosedGaussOutputLinearPolynomial H I E cS))
    (α β : E)
    (hprod : (algebraMap E (N).functionField α * (∑ i, algebraMap E (N).functionField (ν i) * w i) +
        algebraMap E (N).functionField β * r) *
          aeval w (extendedClosedGaussOutputLinearPolynomial H I E cN) = r ^ (d + 1))
    (bS bN : Fin 4 → E)
    (hspan : ∀ i, aeval w (MvPolynomial.map (extendedClosedGaussSourceCoefficientHom H I E) (H i)) =
      algebraMap E (N).functionField (bS i) * aeval w (extendedClosedGaussOutputLinearPolynomial H I E cS) +
        algebraMap E (N).functionField (bN i) * aeval w (extendedClosedGaussOutputLinearPolynomial H I E cN))
    (z : N) (hcodim : Order.coheight ((m) z) = 1) (a : Fin 4) (ha : z ∈ V a)
    (hvan : (N).presheaf.germ (V a) z ha
        (extendedClosedGaussHyperplaneGlobalCoefficient H I E hH e
          (extendedClosedGaussRootCombinationSection H I E hH e ν cS r hd hroot α β) a) ∈
      IsLocalRing.maximalIdeal ((N).presheaf.stalk z))
    (P : Fin 4 → MvPolynomial (Fin 4) K) (g : MvPolynomial (Fin 4) K) {c fdeg : ℕ}
    (hg : g ≠ 0) (hgh : g.IsHomogeneous c) (hP : IsHomogMap P fdeg)
    (hprim : IsPrimitiveVec P) (hHP : H = fun i => g * P i)
    (hdegree : D ≤ d - g.totalDegree) : False := by
  obtain ⟨hD, Δ, _hΔ, _hΔhom, _hdiv, _hdeg, hsmall⟩ :=
    actual_native_pencil_output_span_common_factor_degree H I E hH e hGauss p q hq0 hrel hpH hqH ht
      ν cS cN r hr hd hroot α β hprod bS bN hspan z hcodim a ha hvan P g hg hgh hP hprim hHP
  omega

end DimensionFourDependence
