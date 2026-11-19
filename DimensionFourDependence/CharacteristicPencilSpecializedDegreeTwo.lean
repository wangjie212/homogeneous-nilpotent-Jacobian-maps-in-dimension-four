import DimensionFourDependence.NativePencilDivisorCurveDegreeExistence
import DimensionFourDependence.OriginalNonlinearPencilDegreeTwo

/-! # The original nonlinear map constructs a positive degree-two actual divisor image -/

namespace DimensionFourDependence

open MvPolynomial AlgebraicGeometry
open scoped TensorProduct

attribute [local instance] MvPolynomial.gradedAlgebra Algebra.TensorProduct.rightAlgebra

universe u

set_option quotPrecheck false
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {K : Type u} [kField : Field K] [kCharZero : CharZero K]
  (H : Fin 4 → MvPolynomial (Fin 4) K) (I : ImageRelationWitness H)
  (E : Type u) [Field E] [Algebra (closedGaussParameterField H I) E]
  [Algebra.IsAlgebraic (closedGaussParameterField H I) E]
  {d : ℕ} (hH : IsHomogMap H d)
  (e : RatFunc K ≃ₐ[K] closedGaussParameterField H I)
  (hd : 1 < d) (hind : ¬ComponentsDependent H) (hGauss : gaussImageDimension H I = 1)

local notation "C₀" => closedGaussParameterField H I
local notation "T₀" a:max => projectiveCoordinateChartAlgebra (C := C₀)
  (rationalCoordinate (K := K) (n := 4)) ((finSuccEquiv' a).symm none) ⊗[C₀] E
local notation "N" => extendedClosedGaussNormalizationScheme H I E hH e
local notation "U₀" a:max => extendedClosedGaussNormalizationChartOpen H I E hH e (finSuccEquiv' a)
local notation "w" => extendedClosedGaussNormalizationHyperplaneWeight H I E hH e
local notation "O" => extendedClosedGaussOutputLinearPolynomial H I E
local notation "z₀" a:max q:max => extendedClosedGaussNormalizationTensorChartPoint H I E hH e (finSuccEquiv' a) q
local notation "ha₀" a:max q:max => extendedClosedGaussNormalizationTensorChartPoint_mem_chart H I E hH e (finSuccEquiv' a) q
local notation "P₀" r:max => pencilCoefficientCurveField (E := E)
  (nativeCharacteristicPencilValue H I E hH e (Nat.lt_trans Nat.zero_lt_one hd) hind hGauss r)

local instance characteristicPencilSpecializedDegreeTwoIntegral : IsIntegral N :=
  extendedClosedGaussNormalizationScheme_isIntegral H I E hH e
noncomputable local instance characteristicPencilSpecializedDegreeTwoAlgebra : Algebra E (N).functionField :=
  extendedClosedGaussOwnFunctionFieldAlgebra H I E hH e

/-- The actual original coordinate image at the specified divisor
has a positive curve degree at most two over the restricted coefficient
residue field. This asserts existence of the degree, not only an upper
bound conditional on such a degree. -/
noncomputable def NativeCharacteristicPencilDivisorPositiveDegreeTwo
    (r : (N).functionField) (a : Fin 4) (q : PrimeSpectrum (normalizationRing (T₀ a)))
    (hz : Order.coheight (z₀ a q) = 1) : Prop :=
  letI := extendedClosedGaussNormalization_divisor_stalk_isDVR H I E hH e (z₀ a q) hz
  letI := coefficientRestrictionResidueAlgebra
    (A := (N).presheaf.stalk (z₀ a q)) (F := (N).functionField) (P₀ r)
  ∃ D' : ℕ, D' ≤ 2 ∧ HasCurveHilbertDegree
    (projectiveFieldPointIdeal
      (E := IsLocalRing.ResidueField (coefficientRestrictionValuationSubring
        (A := (N).presheaf.stalk (z₀ a q)) (F := (N).functionField) (P₀ r)))
      (fun i => IsLocalRing.residue ((N).presheaf.stalk (z₀ a q))
        (nativeProjectiveCoordinateGerm H I E hH e (z₀ a q) a (ha₀ a q) i))).toIdeal D'

/-- The same characteristic root carries both its actual generic
pencil curve and an actual root-zero divisor whose original-coordinate
source image has its own positive degree at most two. -/
noncomputable def ActualCharacteristicGaussPositiveDegreeTwoSpecializationData : Prop :=
  ∃ (cS cN : Fin 4 → E) (r : (N).functionField), cS ≠ 0 ∧ cN ≠ 0 ∧ r ≠ 0 ∧
    ∃ hroot : r ^ d = aeval (w) ((O) cS),
      CharacteristicNativeRulingRootFactorization H I E hH e
        (Nat.lt_trans Nat.zero_lt_one hd) hind hGauss cN r ∧
      HasActualGaussRootNumerator H I E e cN ∧
      (∃ D : ℕ, D ≤ 2 ∧ HasCurveHilbertDegree
        (projectiveFieldPointIdeal (E := P₀ r) (w)).toIdeal D) ∧
      ∃ (a : Fin 4) (q : PrimeSpectrum (normalizationRing (T₀ a)))
        (_hq : q.asIdeal.height = 1) (hz : Order.coheight (z₀ a q) = 1),
        (N).presheaf.germ (U₀ a) (z₀ a q) (ha₀ a q)
          (extendedClosedGaussHyperplaneGlobalCoefficient H I E hH e
            (extendedClosedGaussOutputLinearRootSection H I E hH e cS r
              (Nat.lt_trans Nat.zero_lt_one hd) hroot) a) ∈
            IsLocalRing.maximalIdeal ((N).presheaf.stalk (z₀ a q)) ∧
        NativeCharacteristicPencilCoefficientResidueAlgebraic H I E hH e
          (Nat.lt_trans Nat.zero_lt_one hd) hind hGauss r (z₀ a q) hz ∧
        NativeCharacteristicPencilDivisorPositiveDegreeTwo H I E hH e hd hind hGauss r a q hz

/-- The actual positive generic degree-two data construct their own
root divisor, algebraic coefficient residue, and positive specialized
curve degree at most two. No divisor or specialized degree is supplied. -/
theorem actual_degree_two_characteristic_pencil_constructs_positive_divisor_specialization
    [Module.Finite C₀ E]
    (hdata : ActualCharacteristicGaussPencilCurveDegreeTwoData H I hH e hd hind hGauss E) :
    ActualCharacteristicGaussPositiveDegreeTwoSpecializationData H I E hH e hd hind hGauss := by
  obtain ⟨cS, cN, r, hS, hN, hr, hroot, hfactor, hnumerator, D, hD2, hD⟩ := hdata
  obtain ⟨a, q, hq, hz, hvan⟩ := actual_native_nonzero_root_section_has_zero_divisor
    H I E hH e hGauss (Nat.lt_trans Nat.zero_lt_one hd) cS r hr hroot
  have hres : NativeCharacteristicPencilCoefficientResidueAlgebraic H I E hH e
      (Nat.lt_trans Nat.zero_lt_one hd) hind hGauss r (z₀ a q) hz :=
    actual_characteristic_pencil_zero_coefficient_residue_isAlgebraic
      H I E hH e hd hind hGauss cS cN r hr hroot hfactor a q hq hvan
  refine ⟨cS, cN, r, hS, hN, hr, hroot, hfactor, hnumerator, ⟨D, hD2, hD⟩,
    a, q, hq, hz, hvan, hres, ?_⟩
  obtain ⟨D', hle, hD'⟩ := actual_characteristic_pencil_divisor_curve_degree_exists
    H I E hH e (Nat.lt_trans Nat.zero_lt_one hd) hind hGauss r a q hq hz hres hD
  exact ⟨D', hle.trans hD2, hD'⟩

end DimensionFourDependence
