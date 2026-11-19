import DimensionFourDependence.ExtendedSourceFormLocalIdeals

/-! # The actual local common multiplicity of the original components after (4.5) -/

namespace DimensionFourDependence

open MvPolynomial AlgebraicGeometry

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

local notation "N" => extendedClosedGaussNormalizationScheme H I E hH e
local notation "V" a:max => extendedClosedGaussNormalizationChartOpen H I E hH e (finSuccEquiv' a)
local notation "w" => extendedClosedGaussNormalizationHyperplaneWeight H I E hH e

local instance extendedOutputSpanMultiplicityIntegral : IsIntegral N :=
  extendedClosedGaussNormalizationScheme_isIntegral H I E hH e
local instance extendedOutputSpanMultiplicityNoetherian : IsNoetherian N :=
  extendedClosedGaussNormalizationScheme_isNoetherian H I E hH e
noncomputable local instance extendedOutputSpanMultiplicityAlgebra : Algebra E (N).functionField :=
  extendedClosedGaussOwnFunctionFieldAlgebra H I E hH e

variable (hGauss : gaussImageDimension H I = 1)
  (p q : MvPolynomial (Fin 4) K) {D : ℕ}
  (hq0 : q ≠ 0) (hrel : IsRelPrime p q) (hpH : p.IsHomogeneous D) (hqH : q.IsHomogeneous D)
  (ht : closedGaussParameterSourceHom H I e RatFunc.X =
    algebraMap _ (FractionRing (MvPolynomial (Fin 4) K)) p /
      algebraMap _ (FractionRing (MvPolynomial (Fin 4) K)) q)

include hGauss hq0 hrel hpH hqH ht in
/-- The actual original source-form germs have the paper's local
ideal-power multiplicities under the original product-power equations.
The natural exponent includes the case D > d, where it is zero. -/
theorem actual_native_pencil_output_forms_product_power_ideal_bounds
    (ν cS cN : Fin 4 → E) (r : (N).functionField) (hr : r ≠ 0) (hd : 0 < d)
    (hroot : r ^ d = aeval w (extendedClosedGaussOutputLinearPolynomial H I E cS))
    (α β : E)
    (hprod : (algebraMap E (N).functionField α * (∑ i, algebraMap E (N).functionField (ν i) * w i) +
        algebraMap E (N).functionField β * r) *
          aeval w (extendedClosedGaussOutputLinearPolynomial H I E cN) = r ^ (d + 1))
    (z : N) (hz : Order.coheight z = 1) (a : Fin 4) (ha : z ∈ V a)
    (hvan : (N).presheaf.germ (V a) z ha
        (extendedClosedGaussHyperplaneGlobalCoefficient H I E hH e
          (extendedClosedGaussRootCombinationSection H I E hH e ν cS r hd hroot α β) a) ∈
      IsLocalRing.maximalIdeal ((N).presheaf.stalk z)) :
    1 ≤ D ∧
      extendedClosedGaussPolynomialCoefficientGerm H I E hH e
        (extendedClosedGaussOutputLinearPolynomial H I E cN) z a ha ∈
          IsLocalRing.maximalIdeal ((N).presheaf.stalk z) ^ (d + 1 - D) ∧
      extendedClosedGaussPolynomialCoefficientGerm H I E hH e
        (extendedClosedGaussOutputLinearPolynomial H I E cS) z a ha ∈
          IsLocalRing.maximalIdeal ((N).presheaf.stalk z) ^ d := by
  obtain ⟨hD, _hrpos, hn, hs⟩ := actual_native_pencil_output_forms_product_power_order_bounds
    H I E hH e hGauss p q hq0 hrel hpH hqH ht ν cS cN r hr hd hroot α β hprod z hz a ha hvan
  refine ⟨hD, ?_, ?_⟩
  · by_cases hlarge : d + 1 ≤ D
    · simp only [Nat.sub_eq_zero_of_le hlarge, pow_zero, Ideal.one_eq_top, Submodule.mem_top]
    · apply (extendedClosedGaussPolynomialCoefficientGerm_mem_maximalIdeal_pow_iff H I E hH e
        (extendedClosedGaussOutputLinearPolynomial H I E cN)
        (extendedClosedGaussOutputLinearPolynomial_homogeneous H I E hH cN) z hz a ha _).mpr
      exact Or.inr (by omega)
  · exact (extendedClosedGaussPolynomialCoefficientGerm_mem_maximalIdeal_pow_iff H I E hH e
      (extendedClosedGaussOutputLinearPolynomial H I E cS)
      (extendedClosedGaussOutputLinearPolynomial_homogeneous H I E hH cS) z hz a ha d).mpr (Or.inr hs)

include hGauss hq0 hrel hpH hqH ht in
/-- If the two independent ruling output forms span the original
component values, every original component has actual regular local
multiplicity at least d+1-D along the chosen divisor of U. No local
order assumptions on the four components are supplied. -/
theorem actual_native_pencil_output_span_common_multiplicity
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
    (z : N) (hz : Order.coheight z = 1) (a : Fin 4) (ha : z ∈ V a)
    (hvan : (N).presheaf.germ (V a) z ha
        (extendedClosedGaussHyperplaneGlobalCoefficient H I E hH e
          (extendedClosedGaussRootCombinationSection H I E hH e ν cS r hd hroot α β) a) ∈
      IsLocalRing.maximalIdeal ((N).presheaf.stalk z)) :
    1 ≤ D ∧ ∀ i,
      extendedClosedGaussPolynomialCoefficientGerm H I E hH e
        (MvPolynomial.map (extendedClosedGaussSourceCoefficientHom H I E) (H i)) z a ha ∈
          IsLocalRing.maximalIdeal ((N).presheaf.stalk z) ^ (d + 1 - D) := by
  obtain ⟨hD, hn, hs⟩ := actual_native_pencil_output_forms_product_power_ideal_bounds
    H I E hH e hGauss p q hq0 hrel hpH hqH ht ν cS cN r hr hd hroot α β hprod z hz a ha hvan
  refine ⟨hD, fun i => ?_⟩
  apply extendedClosedGaussPolynomialCoefficientGerm_mem_ideal_of_linear_combination H I E hH e
    (MvPolynomial.map (extendedClosedGaussSourceCoefficientHom H I E) (H i))
    (extendedClosedGaussOutputLinearPolynomial H I E cS)
    (extendedClosedGaussOutputLinearPolynomial H I E cN)
    ((hH i).map (extendedClosedGaussSourceCoefficientHom H I E))
    (extendedClosedGaussOutputLinearPolynomial_homogeneous H I E hH cS)
    (extendedClosedGaussOutputLinearPolynomial_homogeneous H I E hH cN)
    (bS i) (bN i) (hspan i) z a ha _ _ hn
  exact Ideal.pow_le_pow_right (by omega : d + 1 - D ≤ d) hs

end DimensionFourDependence
