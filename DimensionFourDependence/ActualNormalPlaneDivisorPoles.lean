import DimensionFourDependence.ActualRootVanishingSourceDivisor
import DimensionFourDependence.FixedVertexScaledPlanePoles

/-! # Actual normal-plane divisors have source-divisor images and quotient poles -/

namespace DimensionFourDependence

open MvPolynomial AlgebraicGeometry
open scoped TensorProduct

attribute [local instance] MvPolynomial.gradedAlgebra Algebra.TensorProduct.rightAlgebra
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
local notation "T" a:max => projectiveCoordinateChartAlgebra (C := C₀)
  (rationalCoordinate (K := K) (n := 4)) ((finSuccEquiv' a).symm none) ⊗[C₀] E
local notation "N" => extendedClosedGaussNormalizationScheme H I E hH e
local notation "V" a:max => extendedClosedGaussNormalizationChartOpen H I E hH e (finSuccEquiv' a)
local notation "z" a:max q:max => extendedClosedGaussNormalizationTensorChartPoint H I E hH e (finSuccEquiv' a) q
local notation "hz" a:max q:max => extendedClosedGaussNormalizationTensorChartPoint_mem_chart H I E hH e (finSuccEquiv' a) q
local notation "w" => extendedClosedGaussNormalizationHyperplaneWeight H I E hH e
local notation "m" => extendedClosedGaussNormalizationSourceMorphism H I E hH e

local instance actualNormalPlaneDivisorPolesIntegral : IsIntegral N :=
  extendedClosedGaussNormalizationScheme_isIntegral H I E hH e
local instance actualNormalPlaneDivisorPolesNonempty (a : Fin 4) : Nonempty (V a) :=
  extendedClosedGaussNormalizationChartOpen_nonempty H I E hH e (finSuccEquiv' a)
noncomputable local instance actualNormalPlaneDivisorPolesAlgebra : Algebra E (N).functionField :=
  extendedClosedGaussOwnFunctionFieldAlgebra H I E hH e

/-- The actual input-linear section germ equals the actual
polynomial coefficient germ at the same canonical normalization point. -/
theorem actual_input_linear_section_germ_eq_polynomial_germ
    (ν : Fin 4 → E) (a : Fin 4) (q : PrimeSpectrum (normalizationRing (T a))) :
    extendedClosedGaussHyperplaneGlobalCoefficientGerm H I E hH e
      (extendedClosedGaussInputLinearSection H I E hH e ν) a q =
      extendedClosedGaussPolynomialCoefficientGerm H I E hH e
        (linearFormPolynomial ν) (z a q) a (hz a q) := by
  apply IsFractionRing.injective ((N).presheaf.stalk (z a q)) (N).functionField
  change algebraMap ((N).presheaf.stalk (z a q)) (N).functionField
    ((N).presheaf.germ (V a) (z a q) (hz a q)
      (extendedClosedGaussHyperplaneGlobalCoefficient H I E hH e
        (extendedClosedGaussInputLinearSection H I E hH e ν) a)) = _
  rw [Scheme.algebraMap_germ_eq_germToFunctionField,
    extendedClosedGaussPolynomialCoefficientGerm_value H I E hH e _ (linearFormPolynomial_homogeneous _)]
  have hgeneric := rationalFrameGlobalCoefficient_generic_value N (fun a : Fin 4 => V a) w
    (extendedClosedGaussNormalizationChartOpen_iSup H I E hH e)
    (extendedClosedGaussNormalizationHyperplaneWeight_ne_zero H I E hH e)
    (extendedClosedGaussInputLinearSection H I E hH e ν) a
  calc
    _ = extendedClosedGaussHyperplaneGlobalValue H I E hH e
        (extendedClosedGaussInputLinearSection H I E hH e ν) / (w) a := hgeneric
    _ = _ := by
      rw [extendedClosedGaussInputLinearSection_value]
      simp only [linearFormPolynomial, map_sum, map_mul, aeval_C, aeval_X, pow_one]

variable (hd : 0 < d) (hind : ¬ComponentsDependent H) (hGauss : gaussImageDimension H I = 1)

local notation "ν₀" => extendedClosedGaussChosenRulingMatrix H I E hH hd hind hGauss 0
local notation "L₀" => linearFormPolynomial (ν₀)

/-- Every height-one canonical normalization divisor in the
actual generic normal plane maps to an original source divisor. Its
source codimension is constructed from the original Gauss-plane incidence. -/
theorem actual_normal_plane_divisor_source_coheight_one
    (a : Fin 4) (q : PrimeSpectrum (normalizationRing (T a))) (hq : q.asIdeal.height = 1)
    (hvan : extendedClosedGaussPolynomialCoefficientGerm H I E hH e (L₀) (z a q) a (hz a q) ∈
      IsLocalRing.maximalIdeal ((N).presheaf.stalk (z a q))) :
    Order.coheight ((m) (z a q)) = 1 := by
  have hinput : extendedClosedGaussHyperplaneGlobalCoefficientGerm H I E hH e
      (extendedClosedGaussInputLinearSection H I E hH e (ν₀)) a q ∈
      IsLocalRing.maximalIdeal ((N).presheaf.stalk (z a q)) := by
    rw [actual_input_linear_section_germ_eq_polynomial_germ]
    exact hvan
  have hplane := extendedClosedGaussInputLinearSection_vanishing_residue_plane
    H I E hH e a q (ν₀) hinput
  have hs := original_tensor_pencil_actual_gauss_plane_source_prime_height_one
    H I E (finSuccEquiv' a) q.asIdeal hH hd hind hGauss e hq hplane
  have hheight := (extendedClosedGaussNormalizationTensorChartPoint_source_height_one_iff
    H I E hH e (finSuccEquiv' a) q).mpr hs
  have hdim := (extendedClosedGaussNormalization_source_stalk_dimension_one_iff
    H I E hH e (finSuccEquiv' a) q).mpr hheight
  rw [ringKrullDim_stalk_eq_coheight] at hdim
  exact_mod_cast hdim

variable [Module.Finite (closedGaussParameterField H I) E]

/-- The exact scaled-plane quotient is nonregular on every actual
canonical normal-plane divisor. The original source-divisor image,
component-span data and primitive common-factor contradiction are all derived. -/
theorem actual_normal_plane_divisor_scaled_quotient_nonregular
    (hvertex : rationalImageNormal H I.equation (Fin.last 3) = 0)
    (s n : Fin 4 → E) (hs : s (Fin.last 3) ≠ 0) (hnlast : n (Fin.last 3) = 0)
    (hn : aeval (w) (extendedClosedGaussOutputLinearPolynomial H I E n) ≠ 0)
    (hL0 : aeval (w) (L₀) ≠ 0) (c : E)
    (hpower : aeval (w) (extendedClosedGaussOutputLinearPolynomial H I E s) =
      algebraMap E (N).functionField c * (aeval (w) (L₀)) ^ d)
    (a : Fin 4) (q : PrimeSpectrum (normalizationRing (T a))) (hq : q.asIdeal.height = 1)
    (hvan : extendedClosedGaussPolynomialCoefficientGerm H I E hH e (L₀) (z a q) a (hz a q) ∈
      IsLocalRing.maximalIdeal ((N).presheaf.stalk (z a q))) :
    ¬ IsLocalization.IsInteger ((N).presheaf.stalk (z a q))
      (aeval (w) (extendedClosedGaussOutputLinearPolynomial H I E n) / (aeval (w) (L₀)) ^ d) := by
  exact actual_fixed_vertex_scaled_plane_quotient_nonregular_over_source_divisor
    H I E hd hH hind hGauss hvertex e s n hs hnlast hn hL0 c hpower (z a q)
    (actual_normal_plane_divisor_source_coheight_one H I E hH e hd hind hGauss a q hq hvan)
    a (hz a q) hvan

end DimensionFourDependence
