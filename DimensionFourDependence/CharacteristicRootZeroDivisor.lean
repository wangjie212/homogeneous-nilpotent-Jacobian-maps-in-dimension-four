import DimensionFourDependence.ExtendedNativeConeZeroTransfer
import DimensionFourDependence.CharacteristicRootSourceDivisorExclusion

/-! # The actual characteristic root has a zero divisor with no source-divisor image -/

namespace DimensionFourDependence

open MvPolynomial AlgebraicGeometry
open scoped TensorProduct

attribute [local instance] Algebra.TensorProduct.rightAlgebra

universe u

set_option quotPrecheck false
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

variable {K : Type u} [Field K] [CharZero K]
  (H : Fin 4 → MvPolynomial (Fin 4) K) (I : ImageRelationWitness H)
  (E : Type u) [Field E] [Algebra (closedGaussParameterField H I) E]
  [Algebra.IsAlgebraic (closedGaussParameterField H I) E]
  {d : ℕ} (hH : IsHomogMap H d)
  (e : RatFunc K ≃ₐ[K] closedGaussParameterField H I)

local notation "C₀" => closedGaussParameterField H I
local notation "T₀" a:max => projectiveCoordinateChartAlgebra (C := C₀)
  (rationalCoordinate (K := K) (n := 4)) ((finSuccEquiv' a).symm none) ⊗[C₀] E
local notation "N" => extendedClosedGaussNormalizationScheme H I E hH e
local notation "U" a:max => extendedClosedGaussNormalizationChartOpen H I E hH e (finSuccEquiv' a)
local notation "w" => extendedClosedGaussNormalizationHyperplaneWeight H I E hH e
local notation "O" => extendedClosedGaussOutputLinearPolynomial H I E
local notation "z₀" a:max q:max => extendedClosedGaussNormalizationTensorChartPoint H I E hH e (finSuccEquiv' a) q
local notation "m" => extendedClosedGaussNormalizationSourceMorphism H I E hH e

local instance characteristicRootZeroDivisorIntegral : IsIntegral N :=
  extendedClosedGaussNormalizationScheme_isIntegral H I E hH e
noncomputable local instance characteristicRootZeroDivisorAlgebra : Algebra E (N).functionField :=
  extendedClosedGaussOwnFunctionFieldAlgebra H I E hH e

/-- A nonzero actual rational root gives an actual zero divisor of
its regular hyperplane section on the original normalized projective pencil. -/
theorem actual_native_nonzero_root_section_has_zero_divisor
    (hGauss : gaussImageDimension H I = 1) (hd : 0 < d)
    (cS : Fin 4 → E) (r : (N).functionField) (hr : r ≠ 0)
    (hroot : r ^ d = aeval w ((O) cS)) :
    ∃ (a : Fin 4) (q : PrimeSpectrum (normalizationRing (T₀ a))), q.asIdeal.height = 1 ∧
      Order.coheight (z₀ a q) = 1 ∧
      (N).presheaf.germ (U a) (z₀ a q)
          (extendedClosedGaussNormalizationTensorChartPoint_mem_chart H I E hH e (finSuccEquiv' a) q)
          (extendedClosedGaussHyperplaneGlobalCoefficient H I E hH e
            (extendedClosedGaussOutputLinearRootSection H I E hH e cS r hd hroot) a) ∈
        IsLocalRing.maximalIdeal ((N).presheaf.stalk (z₀ a q)) := by
  have hnonzero : extendedClosedGaussHyperplaneGlobalValue H I E hH e
      (extendedClosedGaussRootCombinationSection H I E hH e 0 cS r hd hroot 0 1) ≠ 0 := by
    simpa only [extendedClosedGaussRootCombinationSection_value, map_zero, map_one,
      zero_mul, one_mul, zero_add] using hr
  obtain ⟨a, q, hq, hcodim, hvan⟩ := actual_native_nonzero_root_combination_has_zero_divisor
    H I E hH e hGauss 0 cS r hd hroot 0 1 hnonzero
  refine ⟨a, q, hq, hcodim, ?_⟩
  have he : extendedClosedGaussHyperplaneGlobalCoefficientGerm H I E hH e
      (extendedClosedGaussRootCombinationSection H I E hH e 0 cS r hd hroot 0 1) a q =
      (N).presheaf.germ (U a) (z₀ a q)
        (extendedClosedGaussNormalizationTensorChartPoint_mem_chart H I E hH e (finSuccEquiv' a) q)
        (extendedClosedGaussHyperplaneGlobalCoefficient H I E hH e
          (extendedClosedGaussOutputLinearRootSection H I E hH e cS r hd hroot) a) := by
    unfold extendedClosedGaussHyperplaneGlobalCoefficientGerm
    apply IsFractionRing.injective ((N).presheaf.stalk (z₀ a q)) (N).functionField
    rw [extendedClosedGaussHyperplaneGlobalCoefficient_germ_value,
      extendedClosedGaussHyperplaneGlobalCoefficient_germ_value,
      extendedClosedGaussRootCombinationSection_value, extendedClosedGaussOutputLinearRootSection_value]
    simp only [map_zero, map_one, zero_mul, one_mul, zero_add]
  rwa [he] at hvan

variable [Module.Finite (closedGaussParameterField H I) E]

/-- The actual characteristic factorization constructs a root zero
divisor, and its original source image is proved not to be a divisor. -/
theorem actual_characteristic_root_constructs_zero_divisor_without_source_divisor_image
    (hd : 1 < d) (hind : ¬ComponentsDependent H) (hGauss : gaussImageDimension H I = 1)
    (cS cN : Fin 4 → E) (r : (N).functionField) (hr : r ≠ 0)
    (hroot : r ^ d = aeval w ((O) cS))
    (hfactor : CharacteristicNativeRulingRootFactorization H I E hH e (by omega) hind hGauss cN r) :
    ∃ (a : Fin 4) (q : PrimeSpectrum (normalizationRing (T₀ a))), q.asIdeal.height = 1 ∧
      Order.coheight (z₀ a q) = 1 ∧
      (N).presheaf.germ (U a) (z₀ a q)
          (extendedClosedGaussNormalizationTensorChartPoint_mem_chart H I E hH e (finSuccEquiv' a) q)
          (extendedClosedGaussHyperplaneGlobalCoefficient H I E hH e
            (extendedClosedGaussOutputLinearRootSection H I E hH e cS r (by omega) hroot) a) ∈
        IsLocalRing.maximalIdeal ((N).presheaf.stalk (z₀ a q)) ∧
      Order.coheight ((m) (z₀ a q)) ≠ 1 := by
  obtain ⟨a, q, hq, hcodim, hvan⟩ := actual_native_nonzero_root_section_has_zero_divisor
    H I E hH e hGauss (by omega) cS r hr hroot
  exact ⟨a, q, hq, hcodim, hvan, characteristic_native_root_zero_source_coheight_ne_one
    H I E hH e hd hind hGauss cS cN r hroot hfactor (z₀ a q) a
      (extendedClosedGaussNormalizationTensorChartPoint_mem_chart H I E hH e (finSuccEquiv' a) q) hvan⟩

end DimensionFourDependence
