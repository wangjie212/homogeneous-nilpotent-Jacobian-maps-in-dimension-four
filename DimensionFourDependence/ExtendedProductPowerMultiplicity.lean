import DimensionFourDependence.ExtendedNativeLinearCombinations

/-! # The local multiplicity estimates in the actual pencil product-power argument -/

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
local notation "M" => extendedClosedGaussNormalizationHyperplaneModuleSheaf H I E hH e
local notation "V" a:max => extendedClosedGaussNormalizationChartOpen H I E hH e (finSuccEquiv' a)
local notation "w" => extendedClosedGaussNormalizationHyperplaneWeight H I E hH e

local instance extendedProductPowerMultiplicityIntegral : IsIntegral N :=
  extendedClosedGaussNormalizationScheme_isIntegral H I E hH e
local instance extendedProductPowerMultiplicityNoetherian : IsNoetherian N :=
  extendedClosedGaussNormalizationScheme_isNoetherian H I E hH e
local instance extendedProductPowerMultiplicityNonempty (a : Fin 4) : Nonempty (V a) :=
  extendedClosedGaussNormalizationChartOpen_nonempty H I E hH e (finSuccEquiv' a)
noncomputable local instance extendedProductPowerMultiplicityAlgebra : Algebra E (N).functionField :=
  extendedClosedGaussOwnFunctionFieldAlgebra H I E hH e

/-- An actual coefficient germ in any original frame has the
global section's original rational coefficient in the scheme field. -/
theorem extendedClosedGaussHyperplaneGlobalCoefficient_germ_value
    (s : Γ(M, ⊤)) (z : N) (a : Fin 4) (ha : z ∈ V a) :
    algebraMap ((N).presheaf.stalk z) (N).functionField
        ((N).presheaf.germ (V a) z ha (extendedClosedGaussHyperplaneGlobalCoefficient H I E hH e s a)) =
      extendedClosedGaussHyperplaneGlobalValue H I E hH e s / w a :=
  (Scheme.algebraMap_germ_eq_germToFunctionField N ha _).trans
    (rationalFrameGlobalCoefficient_generic_value N (fun a : Fin 4 => V a) w
      (extendedClosedGaussNormalizationChartOpen_iSup H I E hH e)
      (extendedClosedGaussNormalizationHyperplaneWeight_ne_zero H I E hH e) s a)

/-- Actual nonzero global sections have nonzero original-frame
coefficient germs at every point, without a supplied affine prime. -/
theorem extendedClosedGaussHyperplaneGlobalCoefficient_germ_ne_zero
    (s : Γ(M, ⊤)) (hs : s ≠ 0) (z : N) (a : Fin 4) (ha : z ∈ V a) :
    (N).presheaf.germ (V a) z ha (extendedClosedGaussHyperplaneGlobalCoefficient H I E hH e s a) ≠ 0 := by
  intro hzero
  apply extendedClosedGaussHyperplaneGlobalCoefficient_ne_zero H I E hH e s hs a
  exact (germ_injective_of_isIntegral N z ha) (hzero.trans (map_zero _).symm)

variable (hGauss : gaussImageDimension H I = 1)
  (p q : MvPolynomial (Fin 4) K) {D : ℕ}
  (hq0 : q ≠ 0) (hrel : IsRelPrime p q) (hpH : p.IsHomogeneous D) (hqH : q.IsHomogeneous D)
  (ht : closedGaussParameterSourceHom H I e RatFunc.X =
    algebraMap _ (FractionRing (MvPolynomial (Fin 4) K)) p /
      algebraMap _ (FractionRing (MvPolynomial (Fin 4) K)) q)

include hGauss hq0 hrel hpH hqH ht in
/-- For actual regular sections on the actual normalized pencil,
U vanishing and U n = r^(d+1) force the paper's original multiplicity
lower bounds. Nonvanishing of U and regularity of n are derived. -/
theorem actual_native_pencil_product_power_order_bounds
    (s : Γ(M, ⊤))
    (t : Γ(extendedClosedGaussHyperplanePowerModuleSheaf H I E hH e d, ⊤))
    (r : (N).functionField) (hr : r ≠ 0)
    (hprod : extendedClosedGaussHyperplaneGlobalValue H I E hH e s *
        rationalFrameGlobalSectionValue N (fun a : Fin 4 => V a) (fun a => w a ^ d) t = r ^ (d + 1))
    (z : N) (hz : Order.coheight z = 1) (a : Fin 4) (ha : z ∈ V a)
    (hvan : (N).presheaf.germ (V a) z ha
      (extendedClosedGaussHyperplaneGlobalCoefficient H I E hH e s a) ∈
        IsLocalRing.maximalIdeal ((N).presheaf.stalk z)) :
    1 ≤ D ∧ 1 ≤ (N).ord (r / w a) z ∧
      (d : ℤ) + 1 - D ≤ (N).ord
        (rationalFrameGlobalSectionValue N (fun a : Fin 4 => V a) (fun a => w a ^ d) t / w a ^ d) z ∧
      (d : ℤ) ≤ (N).ord ((r / w a) ^ d) z := by
  have hu : extendedClosedGaussHyperplaneGlobalValue H I E hH e s ≠ 0 :=
    (mul_ne_zero_iff.mp (hprod ▸ pow_ne_zero (d + 1) hr)).1
  have hs : s ≠ 0 := by
    intro hzero
    apply hu
    subst s
    rfl
  let : IsDiscreteValuationRing ((N).presheaf.stalk z) :=
    extendedClosedGaussNormalization_divisor_stalk_isDVR H I E hH e z hz
  have hpos := (scheme_regular_integer_order_positive_iff z hz _
    (extendedClosedGaussHyperplaneGlobalCoefficient_germ_ne_zero H I E hH e s hs z a ha)).mpr hvan
  rw [extendedClosedGaussHyperplaneGlobalCoefficient_germ_value H I E hH e s z a ha] at hpos
  have hbound := actual_native_pencil_global_section_every_frame_multiplicity_bound H I E hH e
    hGauss p q hq0 hrel hpH hqH ht s hs z hz a ha
  have hregular := extendedClosedGaussPowerSection_integer_order_nonneg H I E hH e t z hz a ha
  have hscaled : (extendedClosedGaussHyperplaneGlobalValue H I E hH e s / w a) *
      (rationalFrameGlobalSectionValue N (fun a : Fin 4 => V a) (fun a => w a ^ d) t / w a ^ d) =
        (r / w a) ^ (d + 1) := by
    rw [div_mul_div_comm, ← pow_succ', hprod, div_pow]
  refine ⟨by have hb := hbound.2; omega, ?_⟩
  exact scheme_integer_order_product_power_lower_bounds z _ _ _
    (div_ne_zero hr (extendedClosedGaussNormalizationHyperplaneWeight_ne_zero H I E hH e a))
    d D hscaled hpos hbound.2 hregular

include hGauss hq0 hrel hpH hqH ht in
/-- The actual section U = α L_t + β r gives the lower bounds for
the original output forms n(H) and s(H), in every original frame at any
intrinsic divisor where U vanishes. Both source-form sections are actual. -/
theorem actual_native_pencil_output_forms_product_power_order_bounds
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
    1 ≤ D ∧ 1 ≤ (N).ord (r / w a) z ∧
      (d : ℤ) + 1 - D ≤ (N).ord
        (aeval w (extendedClosedGaussOutputLinearPolynomial H I E cN) / w a ^ d) z ∧
      (d : ℤ) ≤ (N).ord
        (aeval w (extendedClosedGaussOutputLinearPolynomial H I E cS) / w a ^ d) z := by
  have hv := extendedClosedGaussRootCombinationSection_value H I E hH e ν cS r hd hroot α β
  have hactual : extendedClosedGaussHyperplaneGlobalValue H I E hH e
      (extendedClosedGaussRootCombinationSection H I E hH e ν cS r hd hroot α β) *
        rationalFrameGlobalSectionValue N (fun a : Fin 4 => V a) (fun a => w a ^ d)
          (extendedClosedGaussOutputLinearSection H I E hH e cN) = r ^ (d + 1) := by
    rw [hv]
    exact hprod
  obtain ⟨hD, hrpos, hn, hs⟩ := actual_native_pencil_product_power_order_bounds H I E hH e hGauss
    p q hq0 hrel hpH hqH ht
    (extendedClosedGaussRootCombinationSection H I E hH e ν cS r hd hroot α β)
    (extendedClosedGaussOutputLinearSection H I E hH e cN) r hr hactual z hz a ha hvan
  refine ⟨hD, hrpos, hn, ?_⟩
  rwa [div_pow, hroot] at hs

end DimensionFourDependence
