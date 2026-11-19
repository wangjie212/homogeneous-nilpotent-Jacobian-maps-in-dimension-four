import DimensionFourDependence.CharacteristicRootMultiplicity
import DimensionFourDependence.NativePencilCommonFactorContradiction
import DimensionFourDependence.PrimitiveMapDegree

/-! # A characteristic-root zero cannot sweep an original source divisor -/

namespace DimensionFourDependence

open MvPolynomial AlgebraicGeometry

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 100000
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
local notation "U" a:max => extendedClosedGaussNormalizationChartOpen H I E hH e (finSuccEquiv' a)
local notation "w" => extendedClosedGaussNormalizationHyperplaneWeight H I E hH e
local notation "O" => extendedClosedGaussOutputLinearPolynomial H I E
local notation "m" => extendedClosedGaussNormalizationSourceMorphism H I E hH e
local notation "ι" => extendedClosedGaussSourceCoefficientHom H I E

local instance characteristicRootSourceDivisorExclusionIntegral : IsIntegral N :=
  extendedClosedGaussNormalizationScheme_isIntegral H I E hH e
noncomputable local instance characteristicRootSourceDivisorExclusionAlgebra : Algebra E (N).functionField :=
  extendedClosedGaussOwnFunctionFieldAlgebra H I E hH e

/-- A zero of the characteristic root section over a source divisor
would force common-factor degree at least d-1. The primitive map has
degree at least two, so the original common factor has degree at most d-2. -/
theorem characteristic_root_zero_cannot_map_to_original_source_divisor
    (hd : 1 < d) (hind : ¬ComponentsDependent H)
    (cS ν V W : Fin 4 → E) (r : (N).functionField)
    (hroot : r ^ d = aeval w ((O) cS))
    (hfactor : ∀ i, aeval w (MvPolynomial.map (ι) (H i)) = r ^ (d - 1) *
      (r * algebraMap E (N).functionField (V i) +
        (∑ j, algebraMap E (N).functionField (ν j) * w j) * algebraMap E (N).functionField (W i)))
    (z : N) (a : Fin 4) (ha : z ∈ U a)
    (hvan : (N).presheaf.germ (U a) z ha
      (extendedClosedGaussHyperplaneGlobalCoefficient H I E hH e
        (extendedClosedGaussOutputLinearRootSection H I E hH e cS r (by omega) hroot) a) ∈
      IsLocalRing.maximalIdeal ((N).presheaf.stalk z)) : Order.coheight ((m) z) ≠ 1 := by
  intro hcodim
  obtain ⟨g, P, c, hc, hg, hgh, hP, hprim, hHP, _hPdegree⟩ :=
    exists_primitive_factorization_common_degree_le_sub_two H hH hind I
  have horders := characteristic_root_zero_original_component_multiplicity
    H I E hH e (by omega) cS ν V W r hroot hfactor z a ha hvan
  obtain ⟨Δ, _hΔ, _hΔhom, _hdiv, _hbound, hsmall⟩ :=
    actual_native_component_orders_common_factor_degree H I E hH e z hcodim a ha
      P g hg hgh hP hprim hHP (d - 1) horders
  have hdegree : g.totalDegree = c := hgh.totalDegree hg
  omega

/-- The same source-divisor exclusion applies directly to the
constructed characteristic native factorization, retaining its root. -/
theorem characteristic_native_root_zero_source_coheight_ne_one
    (hd : 1 < d) (hind : ¬ComponentsDependent H) (hGauss : gaussImageDimension H I = 1)
    (cS cN : Fin 4 → E) (r : (N).functionField)
    (hroot : r ^ d = aeval w ((O) cS))
    (hfactor : CharacteristicNativeRulingRootFactorization H I E hH e (by omega) hind hGauss cN r)
    (z : N) (a : Fin 4) (ha : z ∈ U a)
    (hvan : (N).presheaf.germ (U a) z ha
      (extendedClosedGaussHyperplaneGlobalCoefficient H I E hH e
        (extendedClosedGaussOutputLinearRootSection H I E hH e cS r (by omega) hroot) a) ∈
      IsLocalRing.maximalIdeal ((N).presheaf.stalk z)) : Order.coheight ((m) z) ≠ 1 := by
  obtain ⟨V, W, _hLI, _hV, _hW, _hchar, _hspan, _hzero, hvalues⟩ := hfactor
  exact characteristic_root_zero_cannot_map_to_original_source_divisor H I E hH e hd hind
    cS (extendedClosedGaussChosenRulingMatrix H I E hH (by omega) hind hGauss 0) V W r
    hroot hvalues z a ha hvan

end DimensionFourDependence
