import DimensionFourDependence.FixedCurvePointFieldDimension
import DimensionFourDependence.CharacteristicRootSourceDivisorExclusion
import DimensionFourDependence.TensorPencilResidueDimensionExact
import DimensionFourDependence.TensorPencilResidueSourcePrime
import DimensionFourDependence.GlobalSourceCodimension

/-! # Each characteristic-root divisor has a fixed original source curve -/

namespace DimensionFourDependence

open MvPolynomial AlgebraicGeometry
open scoped TensorProduct

attribute [local instance] Algebra.TensorProduct.rightAlgebra MvPolynomial.gradedAlgebra
attribute [local instance] tensorPencilResidueGenerationNormalizationRing
  tensorPencilResidueGenerationResidueField tensorPencilResidueGenerationCoordinateAlgebra
  tensorPencilResidueGenerationCoordinateSMul tensorPencilResidueGenerationSourceTower
  tensorPencilResidueGenerationExtendedAlgebra tensorPencilResidueGenerationClosedAlgebra
  tensorPencilResidueGenerationClosedSMul tensorPencilResidueGenerationExtendedSMul
  tensorPencilResidueGenerationClosedTower tensorPencilResidueGenerationOriginalSMul
  tensorPencilResidueGenerationOriginalTower
attribute [local instance 2000] originalTensorPencilResidueOriginalAlgebra
attribute [local instance 2000] tensorPencilResiduePointAddCommMonoid
  tensorPencilResiduePointSemiring tensorPencilResiduePointOriginalModule
  tensorPencilResiduePointOriginalMulAction

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
local notation "F₀" a:max q:max => originalTensorPencilResiduePointField H I E (finSuccEquiv' a) (q).asIdeal
local notation "t₀" a:max q:max e₀:max => originalTensorPencilResidueGaussParameter H I E (finSuccEquiv' a) (q).asIdeal e₀

local instance characteristicRootFixedSourceCurveIntegral : IsIntegral N :=
  extendedClosedGaussNormalizationScheme_isIntegral H I E hH e
noncomputable local instance characteristicRootFixedSourceCurveAlgebra : Algebra E (N).functionField :=
  extendedClosedGaussOwnFunctionFieldAlgebra H I E hH e

/-- A divisor of the actual normalized Gauss-pencil surface whose
source image is not a divisor has a one-dimensional original source
point field. The actual Gauss parameter is transcendental over that field. -/
theorem actual_pencil_divisor_without_source_divisor_has_fixed_curve_point_field
    (hGauss : gaussImageDimension H I = 1)
    (e₀ : RatFunc K ≃ₐ[K] projectiveRatioField (K := K)
      (rationalImageNormal H I.equation) (imageNormalPivot H I))
    (a : Fin 4) (q : PrimeSpectrum (normalizationRing (T₀ a))) (hq : q.asIdeal.height = 1)
    (hnot : Order.coheight ((m) (z₀ a q)) ≠ 1) :
    Algebra.trdeg K (F₀ a q) = 1 ∧ Transcendental (F₀ a q) (t₀ a q e₀) := by
  have hfull := original_tensor_pencil_divisor_residue_trdeg_eq_two H I E hH e hGauss
    (finSuccEquiv' a) q.asIdeal hq
  let hgen := original_tensor_pencil_residue_isAlgebraic_over_point_and_parameter
    H I E (finSuccEquiv' a) q.asIdeal e₀
  have hne : Algebra.trdeg K (F₀ a q) ≠ 2 := by
    intro hdim
    have hp := coordinate_relation_prime_height_one_of_generated_field_trdeg_two
      (originalTensorPencilResidueCoordinate H I E (finSuccEquiv' a) q.asIdeal) hdim
    have hprime := (original_tensor_pencil_residue_source_prime_height_eq
      H I E (finSuccEquiv' a) q.asIdeal).trans hp
    have hglobal := (extendedClosedGaussNormalizationTensorChartPoint_source_height_one_iff
      H I E hH e (finSuccEquiv' a) q).mpr hprime
    have hdimSource := (extendedClosedGaussNormalization_source_stalk_dimension_one_iff
      H I E hH e (finSuccEquiv' a) q).mpr hglobal
    apply hnot
    rw [ringKrullDim_stalk_eq_coheight] at hdimSource
    exact_mod_cast hdimSource
  exact surface_point_field_dimension_one_and_parameter_transcendental_of_ne_two
    (t₀ a q e₀) hfull hne

variable [Module.Finite (closedGaussParameterField H I) E]

/-- Every actual characteristic-root zero divisor has a fixed curve
as its original source point field; its parameter remains independent.
Neither the source dimension nor parameter transcendence is assumed. -/
theorem characteristic_root_zero_divisor_constructs_fixed_source_curve_point_field
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
    Algebra.trdeg K (F₀ a q) = 1 ∧
      Transcendental (F₀ a q)
        (t₀ a q (actualGaussRulingParameterChoice H I hH (by omega) hind hGauss)) := by
  exact actual_pencil_divisor_without_source_divisor_has_fixed_curve_point_field H I E hH e hGauss
    (actualGaussRulingParameterChoice H I hH (by omega) hind hGauss) a q hq
    (characteristic_native_root_zero_source_coheight_ne_one H I E hH e hd hind hGauss
      cS cN r hroot hfactor (z₀ a q) a
      (extendedClosedGaussNormalizationTensorChartPoint_mem_chart H I E hH e (finSuccEquiv' a) q) hvan)

end DimensionFourDependence
