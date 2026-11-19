import DimensionFourDependence.TensorPencilActualGaussPlane
import DimensionFourDependence.ExtendedRootCombinationVanishing
import DimensionFourDependence.ExtendedInputLinearResidue
import DimensionFourDependence.GlobalSourceCodimension

/-! # Every actual zero divisor of the Gauss root combination has a source divisor image -/

namespace DimensionFourDependence

universe u

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

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option quotPrecheck false

variable {K : Type u} [Field K] [CharZero K]
  (H : Fin 4 → MvPolynomial (Fin 4) K) (I : ImageRelationWitness H)
  (E : Type u) [Field E] [Algebra (closedGaussParameterField H I) E]
  [Algebra.IsAlgebraic (closedGaussParameterField H I) E]
  {d : ℕ} (hH : IsHomogMap H d)
  (e : RatFunc K ≃ₐ[K] closedGaussParameterField H I)
  (hd : 0 < d) (hind : ¬ ComponentsDependent H) (hGauss : gaussImageDimension H I = 1)

local notation "C₀" => closedGaussParameterField H I
local notation "T₀" a:max => projectiveCoordinateChartAlgebra (C := C₀)
  (rationalCoordinate (K := K) (n := 4)) ((finSuccEquiv' a).symm none) ⊗[C₀] E
local notation "N" => extendedClosedGaussNormalizationScheme H I E hH e
local notation "V" a:max => extendedClosedGaussNormalizationChartOpen H I E hH e (finSuccEquiv' a)
local notation "w" => extendedClosedGaussNormalizationHyperplaneWeight H I E hH e
local notation "ν₀" => extendedClosedGaussChosenRulingMatrix H I E hH hd hind hGauss 0

local instance actualRootVanishingSourceDivisorIntegral : IsIntegral N :=
  extendedClosedGaussNormalizationScheme_isIntegral H I E hH e
noncomputable local instance actualRootVanishingSourceDivisorAlgebra : Algebra E (N).functionField :=
  extendedClosedGaussOwnFunctionFieldAlgebra H I E hH e

/-- Every given actual zero divisor of U has a height-one original
source contraction. The actual Gauss-plane incidence, residue field
generation, source dimension, and source codimension are all derived. -/
theorem actual_native_gauss_root_zero_source_prime_height_one
    (a : Fin 4) (q : PrimeSpectrum (normalizationRing (T₀ a))) (hq : q.asIdeal.height = 1)
    (cS cN : Fin 4 → E) (r : (N).functionField)
    (hroot : r ^ d = aeval w (extendedClosedGaussOutputLinearPolynomial H I E cS))
    (α β : E) (hα : α ≠ 0)
    (hprod : extendedClosedGaussHyperplaneGlobalValue H I E hH e
        (extendedClosedGaussRootCombinationSection H I E hH e ν₀ cS r hd hroot α β) *
          aeval w (extendedClosedGaussOutputLinearPolynomial H I E cN) = r ^ (d + 1))
    (hvan : extendedClosedGaussHyperplaneGlobalCoefficientGerm H I E hH e
      (extendedClosedGaussRootCombinationSection H I E hH e ν₀ cS r hd hroot α β) a q ∈
        IsLocalRing.maximalIdeal ((N).presheaf.stalk
          (extendedClosedGaussNormalizationTensorChartPoint H I E hH e (finSuccEquiv' a) q))) :
    (q.asIdeal.comap (extendedClosedGaussTensorNormalizationSourceHom H I E (finSuccEquiv' a))).height = 1 := by
  have hL := (actual_native_root_combination_vanishing H I E hH e ν₀ cS cN r hd hroot α β hα hprod
    (extendedClosedGaussNormalizationTensorChartPoint H I E hH e (finSuccEquiv' a) q) a
    (extendedClosedGaussNormalizationTensorChartPoint_mem_chart H I E hH e (finSuccEquiv' a) q) hvan).2
  have hplane := extendedClosedGaussInputLinearSection_vanishing_residue_plane H I E hH e a q ν₀ hL
  exact original_tensor_pencil_actual_gauss_plane_source_prime_height_one
    H I E (finSuccEquiv' a) q.asIdeal hH hd hind hGauss e hq hplane

/-- The codimension-one source image holds in the actual original
projective space at the actual global point of the normalization. -/
theorem actual_native_gauss_root_zero_global_source_height_one
    (a : Fin 4) (q : PrimeSpectrum (normalizationRing (T₀ a))) (hq : q.asIdeal.height = 1)
    (cS cN : Fin 4 → E) (r : (N).functionField)
    (hroot : r ^ d = aeval w (extendedClosedGaussOutputLinearPolynomial H I E cS))
    (α β : E) (hα : α ≠ 0)
    (hprod : extendedClosedGaussHyperplaneGlobalValue H I E hH e
        (extendedClosedGaussRootCombinationSection H I E hH e ν₀ cS r hd hroot α β) *
          aeval w (extendedClosedGaussOutputLinearPolynomial H I E cN) = r ^ (d + 1))
    (hvan : extendedClosedGaussHyperplaneGlobalCoefficientGerm H I E hH e
      (extendedClosedGaussRootCombinationSection H I E hH e ν₀ cS r hd hroot α β) a q ∈
        IsLocalRing.maximalIdeal ((N).presheaf.stalk
          (extendedClosedGaussNormalizationTensorChartPoint H I E hH e (finSuccEquiv' a) q))) :
    ((Proj.isAffineOpen_basicOpen (homogeneousSubmodule (Fin 4) K)
      (X ((finSuccEquiv' a).symm none)) (isHomogeneous_X (R := K) _) (by omega)).primeIdealOf
        ⟨extendedClosedGaussNormalizationSourceMorphism H I E hH e
          (extendedClosedGaussNormalizationTensorChartPoint H I E hH e (finSuccEquiv' a) q),
          extendedClosedGaussNormalizationTensorChartPoint_source_mem H I E hH e (finSuccEquiv' a) q⟩).asIdeal.height = 1 :=
  (extendedClosedGaussNormalizationTensorChartPoint_source_height_one_iff H I E hH e (finSuccEquiv' a) q).mpr
    (actual_native_gauss_root_zero_source_prime_height_one H I E hH e hd hind hGauss
      a q hq cS cN r hroot α β hα hprod hvan)

/-- The source-image point is intrinsically a divisor point of
the original projective space, without a selected affine height hypothesis. -/
theorem actual_native_gauss_root_zero_source_coheight_one
    (a : Fin 4) (q : PrimeSpectrum (normalizationRing (T₀ a))) (hq : q.asIdeal.height = 1)
    (cS cN : Fin 4 → E) (r : (N).functionField)
    (hroot : r ^ d = aeval w (extendedClosedGaussOutputLinearPolynomial H I E cS))
    (α β : E) (hα : α ≠ 0)
    (hprod : extendedClosedGaussHyperplaneGlobalValue H I E hH e
        (extendedClosedGaussRootCombinationSection H I E hH e ν₀ cS r hd hroot α β) *
          aeval w (extendedClosedGaussOutputLinearPolynomial H I E cN) = r ^ (d + 1))
    (hvan : extendedClosedGaussHyperplaneGlobalCoefficientGerm H I E hH e
      (extendedClosedGaussRootCombinationSection H I E hH e ν₀ cS r hd hroot α β) a q ∈
        IsLocalRing.maximalIdeal ((N).presheaf.stalk
          (extendedClosedGaussNormalizationTensorChartPoint H I E hH e (finSuccEquiv' a) q))) :
    Order.coheight (extendedClosedGaussNormalizationSourceMorphism H I E hH e
      (extendedClosedGaussNormalizationTensorChartPoint H I E hH e (finSuccEquiv' a) q)) = 1 := by
  have hdim := (extendedClosedGaussNormalization_source_stalk_dimension_one_iff H I E hH e
    (finSuccEquiv' a) q).mpr
      (actual_native_gauss_root_zero_global_source_height_one H I E hH e hd hind hGauss
        a q hq cS cN r hroot α β hα hprod hvan)
  rw [ringKrullDim_stalk_eq_coheight] at hdim
  exact_mod_cast hdim

/-- The paper's rational root formula and binary-form equation
already supply the product identity. Thus every given zero divisor of
its actual U has a source divisor image without an image hypothesis. -/
theorem actual_native_gauss_rational_root_zero_source_prime_height_one
    (a : Fin 4) (q : PrimeSpectrum (normalizationRing (T₀ a))) (hq : q.asIdeal.height = 1)
    (cS cM cN : Fin 4 → E) (r : (N).functionField)
    (hroot : r ^ d = aeval w (extendedClosedGaussOutputLinearPolynomial H I E cS))
    (α β : E) (hα : α ≠ 0)
    (hlinear : aeval w (extendedClosedGaussOutputLinearPolynomial H I E cS) =
      algebraMap E (N).functionField α * aeval w (extendedClosedGaussOutputLinearPolynomial H I E cM) +
        algebraMap E (N).functionField β * aeval w (extendedClosedGaussOutputLinearPolynomial H I E cN))
    (hm : aeval w (extendedClosedGaussOutputLinearPolynomial H I E cM) ≠ 0)
    (hformula : r = aeval w (extendedClosedGaussOutputLinearPolynomial H I E cN) *
      (∑ i, algebraMap E (N).functionField (ν₀ i) * w i) /
        aeval w (extendedClosedGaussOutputLinearPolynomial H I E cM))
    (hvan : extendedClosedGaussHyperplaneGlobalCoefficientGerm H I E hH e
      (extendedClosedGaussRootCombinationSection H I E hH e ν₀ cS r hd hroot α β) a q ∈
        IsLocalRing.maximalIdeal ((N).presheaf.stalk
          (extendedClosedGaussNormalizationTensorChartPoint H I E hH e (finSuccEquiv' a) q))) :
    (q.asIdeal.comap (extendedClosedGaussTensorNormalizationSourceHom H I E (finSuccEquiv' a))).height = 1 :=
  actual_native_gauss_root_zero_source_prime_height_one H I E hH e hd hind hGauss
    a q hq cS cN r hroot α β hα
    (actual_native_root_combination_product_power_of_rational_root_formula H I E hH e
      ν₀ cS cM cN r hd hroot α β hlinear hm hformula) hvan

end DimensionFourDependence
