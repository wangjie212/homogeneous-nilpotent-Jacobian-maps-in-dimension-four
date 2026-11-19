import DimensionFourDependence.FixedCurveCoefficientDegreeDescent
import DimensionFourDependence.CharacteristicRootFixedSourceCurve
import DimensionFourDependence.RestoredCoordinateField

/-! # The actual characteristic-root source curve retains its degree over original constants -/

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
  tensorPencilResiduePointAddCommMonoid tensorPencilResiduePointSemiring
  tensorPencilResiduePointOriginalModule tensorPencilResiduePointOriginalMulAction

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
local notation "F₀" a:max q:max => FractionRing (normalizationRing (T₀ a) ⧸ (q).asIdeal)
local notation "y₀" a:max q:max => originalTensorPencilResidueCoordinate H I E (finSuccEquiv' a) (q).asIdeal
local notation "z₀" a:max q:max => fun i : Fin 4 => (finSuccEquiv' a i).elim 1 (y₀ a q)
local notation "N" => extendedClosedGaussNormalizationScheme H I E hH e
local notation "w" => extendedClosedGaussNormalizationHyperplaneWeight H I E hH e
local notation "O" => extendedClosedGaussOutputLinearPolynomial H I E
local notation "zₙ" a:max q:max => extendedClosedGaussNormalizationTensorChartPoint H I E hH e (finSuccEquiv' a) q
local notation "U₀" a:max => extendedClosedGaussNormalizationChartOpen H I E hH e (finSuccEquiv' a)

local instance originalRootFixedCurveDegreeIntegral : IsIntegral N :=
  extendedClosedGaussNormalizationScheme_isIntegral H I E hH e
noncomputable local instance originalRootFixedCurveDegreeAlgebra : Algebra E (N).functionField :=
  extendedClosedGaussOwnFunctionFieldAlgebra H I E hH e

include hH e in
/-- An actual tensor-normalization surface divisor has an original
affine source coordinate transcendental over the same extended constants. -/
theorem original_tensor_divisor_has_transcendental_source_coordinate
    (hGauss : gaussImageDimension H I = 1)
    (a : Fin 4) (q : PrimeSpectrum (normalizationRing (T₀ a))) (hq : q.asIdeal.height = 1) :
    ∃ i : Fin 3, Transcendental E ((y₀ a q) i) := by
  have htr := original_tensor_pencil_divisor_residue_relative_trdeg_eq_one
    H I E hH e hGauss (finSuccEquiv' a) q.asIdeal hq
  by_contra hn
  have hx (i : Fin 3) : IsAlgebraic E ((y₀ a q) i) := not_not.mp (not_exists.mp hn i)
  letI : Algebra.IsAlgebraic E (F₀ a q) :=
    normalization_prime_residue_fraction_field_isAlgebraic (J := E) q.asIdeal
      (originalTensorPencilCoordinate H I E (finSuccEquiv' a))
      (originalTensorPencilCoordinate_adjoin H I E (finSuccEquiv' a))
      (fun c => isAlgebraic_algebraMap c) hx
  have hz : Algebra.trdeg E (F₀ a q) = 0 := trdeg_eq_zero
  rw [htr] at hz
  exact one_ne_zero hz

/-- For the actual characteristic-root zero divisor, every original
source-coordinate Hilbert function is unchanged after any compatible
algebraic extension of the extended Gauss constants. In particular a
positive specialized degree at most two is the fixed original source
curve's degree over the original algebraically closed constants. -/
theorem actual_characteristic_root_fixed_source_hilbert_eq_algebraic_coefficients
    [IsAlgClosed K] [Module.Finite C₀ E]
    (hd : 1 < d) (hind : ¬ComponentsDependent H) (hGauss : gaussImageDimension H I = 1)
    (cS cN : Fin 4 → E) (r : (N).functionField)
    (hroot : r ^ d = aeval (w) ((O) cS))
    (hfactor : CharacteristicNativeRulingRootFactorization H I E hH e
      (Nat.lt_trans Nat.zero_lt_one hd) hind hGauss cN r)
    (a : Fin 4) (q : PrimeSpectrum (normalizationRing (T₀ a))) (hq : q.asIdeal.height = 1)
    (hvan : (N).presheaf.germ (U₀ a) (zₙ a q)
      (extendedClosedGaussNormalizationTensorChartPoint_mem_chart H I E hH e (finSuccEquiv' a) q)
      (extendedClosedGaussHyperplaneGlobalCoefficient H I E hH e
        (extendedClosedGaussOutputLinearRootSection H I E hH e cS r
          (Nat.lt_trans Nat.zero_lt_one hd) hroot) a) ∈
      IsLocalRing.maximalIdeal ((N).presheaf.stalk (zₙ a q)))
    (C : Type u) [Field C] [Algebra E C] [Algebra.IsAlgebraic E C]
    (aCF : Algebra C (F₀ a q))
    (hTower : letI : Algebra C (F₀ a q) := aCF
      letI : SMul C (F₀ a q) := aCF.toSMul
      IsScalarTower E C (F₀ a q)) (n : ℕ) :
    letI : Algebra C (F₀ a q) := aCF
    letI : SMul C (F₀ a q) := aCF.toSMul
    projectiveHilbertFunction (projectiveFieldPointIdeal (E := C) (z₀ a q)).toIdeal n =
      projectiveHilbertFunction (projectiveFieldPointIdeal (E := K) (z₀ a q)).toIdeal n := by
  have htrans : ∃ j : Fin 4, Transcendental E ((z₀ a q) j) :=
    exists_restored_projective_coordinate_of_affine (Transcendental E)
      (finSuccEquiv' a) (y₀ a q)
      (original_tensor_divisor_has_transcendental_source_coordinate H I E hH e hGauss a q hq)
  letI : Algebra C (F₀ a q) := aCF
  letI : SMul C (F₀ a q) := aCF.toSMul
  letI : Algebra E (F₀ a q) := normalizationPrimeResidueCoefficientAlgebra (E := E) q.asIdeal
  letI : SMul E (F₀ a q) :=
    (normalizationPrimeResidueCoefficientAlgebra (E := E) q.asIdeal).toSMul
  letI : Algebra K (F₀ a q) :=
    originalTensorPencilResidueOriginalAlgebra H I E (finSuccEquiv' a) q.asIdeal
  letI : SMul K (F₀ a q) :=
    (originalTensorPencilResidueOriginalAlgebra H I E (finSuccEquiv' a) q.asIdeal).toSMul
  letI : IsScalarTower E C (F₀ a q) := hTower
  have hdim := (characteristic_root_zero_divisor_constructs_fixed_source_curve_point_field
    H I E hH e hd hind hGauss cS cN r hroot hfactor a q hq hvan).1
  have hcurve : Algebra.trdeg K (IntermediateField.adjoin K (Set.range (z₀ a q))) ≤ 1 := by
    have he := congrArg (fun J : IntermediateField K (F₀ a q) => Algebra.trdeg K J)
      (adjoin_restored_projective_coordinates_eq (K := K) (finSuccEquiv' a) (y₀ a q))
    exact he.le.trans hdim.le
  let ι := extendedClosedGaussSourceCoefficientHom H I E
  letI : Algebra K E := ι.toAlgebra
  letI : SMul K E := ι.toAlgebra.toSMul
  letI : Algebra K C := ((algebraMap E C).comp ι).toAlgebra
  letI : SMul K C := (inferInstance : Algebra K C).toSMul
  letI : IsScalarTower K E C := IsScalarTower.of_algebraMap_eq' rfl
  letI : IsScalarTower K E (F₀ a q) := IsScalarTower.of_algebraMap_eq (fun c => by
    change algebraMap C₀ (F₀ a q) (algebraMap K C₀ c) =
      algebraMap E (F₀ a q) (ι c)
    exact IsScalarTower.algebraMap_apply C₀ E (F₀ a q) _)
  letI : IsScalarTower K C (F₀ a q) := IsScalarTower.of_algebraMap_eq (fun c => by
    change algebraMap K (F₀ a q) c =
      algebraMap C (F₀ a q) (algebraMap E C (ι c))
    exact (IsScalarTower.algebraMap_apply K E (F₀ a q) c).trans
      (IsScalarTower.algebraMap_apply E C (F₀ a q) (ι c)))
  exact fixed_curve_projective_hilbert_eq_algebraic_coefficients
    (C := C) (E := E) (z₀ a q) hcurve htrans n

end DimensionFourDependence
