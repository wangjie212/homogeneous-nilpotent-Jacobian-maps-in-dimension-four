import DimensionFourDependence.NativePencilCommonFactorContradiction
import DimensionFourDependence.ReducedHomogeneousPencilDegree
import DimensionFourDependence.NativePencilSpreadFamily
import DimensionFourDependence.RulingRootProductIdentity

/-! # The product-power branch is excluded under the actual spread-out source-image hypothesis -/

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

local instance nativePencilSourceDivisorExclusionIntegral : IsIntegral N :=
  extendedClosedGaussNormalizationScheme_isIntegral H I E hH e
noncomputable local instance nativePencilSourceDivisorExclusionAlgebra : Algebra E (N).functionField :=
  extendedClosedGaussOwnFunctionFieldAlgebra H I E hH e

variable (hGauss : gaussImageDimension H I = 1)
  (p q : MvPolynomial (Fin 4) K) {D : ℕ}
  (hq0 : q ≠ 0) (hrel : IsRelPrime p q) (hpH : p.IsHomogeneous D) (hqH : q.IsHomogeneous D)
  (ht : closedGaussParameterSourceHom H I e RatFunc.X =
    algebraMap _ (FractionRing (MvPolynomial (Fin 4) K)) p /
      algebraMap _ (FractionRing (MvPolynomial (Fin 4) K)) q)

include hGauss hq0 hrel hpH hqH ht in
/-- The original nonplanar homogeneous map excludes the product-power
configuration at a zero of U over a source divisor. Both the pencil-degree
upper bound and every common-factor lower bound are derived. -/
theorem no_actual_nonplanar_native_pencil_output_span_source_divisor
    (hind : ¬ ComponentsDependent H)
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
    (hprim : IsPrimitiveVec P) (hHP : H = fun i => g * P i) : False := by
  have hdegree := actual_closed_gauss_given_parameter_pencil_degree_le_degree_sub_common_factor
    H hd hH hind I e g hg P hP hHP p q hq0 hrel hqH ht
  exact no_actual_native_pencil_output_span_product_power_source_divisor H I E hH e hGauss
    p q hq0 hrel hpH hqH ht ν cS cN r hr hd hroot α β hprod bS bN hspan z hcodim a ha hvan
    P g hg hgh hP hprim hHP hdegree

include hGauss hq0 hrel hpH hqH ht in
/-- A prime subvariety on which U vanishes cannot have an actual
spread-out family dense in an original source divisor under the paper's
product-power and ruling-span equations. The parameter model is arbitrary
with its specified field point; no source-point, component-order or
numerical pencil-degree comparison is assumed separately. -/
theorem no_actual_native_pencil_product_power_spread_source_divisor
    (hind : ¬ ComponentsDependent H)
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
    (model : ClosedGaussParameterSchemeModel H I E)
    (Z : Set N) (hZ : IsIrreducible Z) (hZclosed : IsClosed Z)
    (D₀ : Set P₀) (hD : IsIrreducible D₀) (hDclosed : IsClosed D₀)
    (hdiv : Order.coheight hD.genericPoint = 1)
    (himage : closure (Set.range
      (nativeClosedGaussPencilSpreadFamilySourceMorphism H I E hH e model Z hZ)) = D₀)
    (a : Fin 4) (ha : hZ.genericPoint ∈ V a)
    (hvan : (N).presheaf.germ (V a) hZ.genericPoint ha
        (extendedClosedGaussHyperplaneGlobalCoefficient H I E hH e
          (extendedClosedGaussRootCombinationSection H I E hH e ν cS r hd hroot α β) a) ∈
      IsLocalRing.maximalIdeal ((N).presheaf.stalk hZ.genericPoint))
    (P : Fin 4 → MvPolynomial (Fin 4) K) (g : MvPolynomial (Fin 4) K) {c fdeg : ℕ}
    (hg : g ≠ 0) (hgh : g.IsHomogeneous c) (hP : IsHomogMap P fdeg)
    (hprim : IsPrimitiveVec P) (hHP : H = fun i => g * P i) : False := by
  have hgeneric : closure ((m) '' Z) = D₀ :=
    (nativeClosedGaussPencilSpreadFamilySourceMorphism_image_closure H I E hH e model Z hZ hZclosed).symm.trans himage
  have hpoint := scheme_generic_point_image_eq m
    (hZ.isGenericPoint_genericPoint hZclosed) (hD.isGenericPoint_genericPoint hDclosed) hgeneric
  have hcodim : Order.coheight ((m) hZ.genericPoint) = 1 := by
    rw [hpoint]
    exact hdiv
  exact no_actual_nonplanar_native_pencil_output_span_source_divisor H I E hH e hGauss
    p q hq0 hrel hpH hqH ht hind ν cS cN r hr hd hroot α β hprod bS bN hspan
    hZ.genericPoint hcodim a ha hvan P g hg hgh hP hprim hHP

include hGauss hq0 hrel hpH hqH ht in
/-- The original root equation and rational formula in (4.4), with
the original binary-form relation, exclude the dense spread-out divisor
configuration. Equation (4.5), all regular section and component orders,
the common-factor bound and the pencil-degree bound are derived. -/
theorem no_actual_native_pencil_rational_root_spread_source_divisor
    (hind : ¬ ComponentsDependent H)
    (ν cS cM cN : Fin 4 → E) (r : (N).functionField) (hr : r ≠ 0) (hd : 0 < d)
    (hroot : r ^ d = aeval w (extendedClosedGaussOutputLinearPolynomial H I E cS))
    (α β : E)
    (hlinear : aeval w (extendedClosedGaussOutputLinearPolynomial H I E cS) =
      algebraMap E (N).functionField α * aeval w (extendedClosedGaussOutputLinearPolynomial H I E cM) +
        algebraMap E (N).functionField β * aeval w (extendedClosedGaussOutputLinearPolynomial H I E cN))
    (hm : aeval w (extendedClosedGaussOutputLinearPolynomial H I E cM) ≠ 0)
    (hformula : r = aeval w (extendedClosedGaussOutputLinearPolynomial H I E cN) *
      (∑ i, algebraMap E (N).functionField (ν i) * w i) /
        aeval w (extendedClosedGaussOutputLinearPolynomial H I E cM))
    (bS bN : Fin 4 → E)
    (hspan : ∀ i, aeval w (MvPolynomial.map (extendedClosedGaussSourceCoefficientHom H I E) (H i)) =
      algebraMap E (N).functionField (bS i) * aeval w (extendedClosedGaussOutputLinearPolynomial H I E cS) +
        algebraMap E (N).functionField (bN i) * aeval w (extendedClosedGaussOutputLinearPolynomial H I E cN))
    (model : ClosedGaussParameterSchemeModel H I E)
    (Z : Set N) (hZ : IsIrreducible Z) (hZclosed : IsClosed Z)
    (D₀ : Set P₀) (hD : IsIrreducible D₀) (hDclosed : IsClosed D₀)
    (hdiv : Order.coheight hD.genericPoint = 1)
    (himage : closure (Set.range
      (nativeClosedGaussPencilSpreadFamilySourceMorphism H I E hH e model Z hZ)) = D₀)
    (a : Fin 4) (ha : hZ.genericPoint ∈ V a)
    (hvan : (N).presheaf.germ (V a) hZ.genericPoint ha
        (extendedClosedGaussHyperplaneGlobalCoefficient H I E hH e
          (extendedClosedGaussRootCombinationSection H I E hH e ν cS r hd hroot α β) a) ∈
      IsLocalRing.maximalIdeal ((N).presheaf.stalk hZ.genericPoint))
    (P : Fin 4 → MvPolynomial (Fin 4) K) (g : MvPolynomial (Fin 4) K) {c fdeg : ℕ}
    (hg : g ≠ 0) (hgh : g.IsHomogeneous c) (hP : IsHomogMap P fdeg)
    (hprim : IsPrimitiveVec P) (hHP : H = fun i => g * P i) : False := by
  have hprod := actual_native_root_combination_product_power_of_rational_root_formula H I E hH e
    ν cS cM cN r hd hroot α β hlinear hm hformula
  rw [extendedClosedGaussRootCombinationSection_value] at hprod
  exact no_actual_native_pencil_product_power_spread_source_divisor H I E hH e hGauss
    p q hq0 hrel hpH hqH ht hind ν cS cN r hr hd hroot α β hprod bS bN hspan
    model Z hZ hZclosed D₀ hD hDclosed hdiv himage a ha hvan P g hg hgh hP hprim hHP

end DimensionFourDependence
