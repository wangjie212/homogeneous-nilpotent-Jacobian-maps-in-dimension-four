import DimensionFourDependence.CharacteristicRootSourceDivisorExclusion
import DimensionFourDependence.ActualRootVanishingSourceDivisor

/-! # The characteristic root and tangent-plane sections have no common divisor -/

namespace DimensionFourDependence

open MvPolynomial AlgebraicGeometry
open scoped TensorProduct

attribute [local instance] MvPolynomial.gradedAlgebra Algebra.TensorProduct.rightAlgebra

universe u

set_option quotPrecheck false
set_option maxHeartbeats 4000000
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

local instance characteristicPencilNoCommonDivisorIntegral : IsIntegral N :=
  extendedClosedGaussNormalizationScheme_isIntegral H I E hH e
noncomputable local instance characteristicPencilNoCommonDivisorAlgebra : Algebra E (N).functionField :=
  extendedClosedGaussOwnFunctionFieldAlgebra H I E hH e

/-- Every actual divisor on which the chosen tangent-plane section
vanishes maps to a divisor of the original projective source. -/
theorem actual_chosen_tangent_plane_zero_divisor_source_coheight_one
    (hd : 0 < d) (hind : ¬ComponentsDependent H) (hGauss : gaussImageDimension H I = 1)
    (a : Fin 4) (q : PrimeSpectrum (normalizationRing (T₀ a))) (hq : q.asIdeal.height = 1)
    (hvan : extendedClosedGaussHyperplaneGlobalCoefficientGerm H I E hH e
      (extendedClosedGaussInputLinearSection H I E hH e
        (extendedClosedGaussChosenRulingMatrix H I E hH hd hind hGauss 0)) a q ∈
        IsLocalRing.maximalIdeal ((N).presheaf.stalk (z₀ a q))) :
    Order.coheight ((m) (z₀ a q)) = 1 := by
  have hplane := extendedClosedGaussInputLinearSection_vanishing_residue_plane H I E hH e a q
    (extendedClosedGaussChosenRulingMatrix H I E hH hd hind hGauss 0) hvan
  have hprime := original_tensor_pencil_actual_gauss_plane_source_prime_height_one
    H I E (finSuccEquiv' a) q.asIdeal hH hd hind hGauss e hq hplane
  have hglobal := (extendedClosedGaussNormalizationTensorChartPoint_source_height_one_iff
    H I E hH e (finSuccEquiv' a) q).mpr hprime
  have hdim := (extendedClosedGaussNormalization_source_stalk_dimension_one_iff
    H I E hH e (finSuccEquiv' a) q).mpr hglobal
  rw [ringKrullDim_stalk_eq_coheight] at hdim
  exact_mod_cast hdim

variable [Module.Finite (closedGaussParameterField H I) E]

/-- At every actual height-one chart prime, vanishing of the root
section excludes vanishing of the chosen tangent-plane section. Thus
the actual characteristic pencil has no common divisor component. -/
theorem characteristic_root_and_tangent_plane_have_no_common_divisor
    (hd : 1 < d) (hind : ¬ComponentsDependent H) (hGauss : gaussImageDimension H I = 1)
    (cS cN : Fin 4 → E) (r : (N).functionField)
    (hroot : r ^ d = aeval w ((O) cS))
    (hfactor : CharacteristicNativeRulingRootFactorization H I E hH e (by omega) hind hGauss cN r)
    (a : Fin 4) (q : PrimeSpectrum (normalizationRing (T₀ a))) (hq : q.asIdeal.height = 1)
    (hvan : (N).presheaf.germ (U a) (z₀ a q)
      (extendedClosedGaussNormalizationTensorChartPoint_mem_chart H I E hH e (finSuccEquiv' a) q)
      (extendedClosedGaussHyperplaneGlobalCoefficient H I E hH e
        (extendedClosedGaussOutputLinearRootSection H I E hH e cS r (by omega) hroot) a) ∈
      IsLocalRing.maximalIdeal ((N).presheaf.stalk (z₀ a q))) :
    extendedClosedGaussHyperplaneGlobalCoefficientGerm H I E hH e
      (extendedClosedGaussInputLinearSection H I E hH e
        (extendedClosedGaussChosenRulingMatrix H I E hH (by omega) hind hGauss 0)) a q ∉
      IsLocalRing.maximalIdeal ((N).presheaf.stalk (z₀ a q)) := by
  intro hplane
  have hnot := characteristic_native_root_zero_source_coheight_ne_one H I E hH e hd hind hGauss
    cS cN r hroot hfactor (z₀ a q) a
      (extendedClosedGaussNormalizationTensorChartPoint_mem_chart H I E hH e (finSuccEquiv' a) q) hvan
  exact hnot (actual_chosen_tangent_plane_zero_divisor_source_coheight_one
    H I E hH e (by omega) hind hGauss a q hq hplane)

end DimensionFourDependence
