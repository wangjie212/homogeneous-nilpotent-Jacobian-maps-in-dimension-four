import DimensionFourDependence.CharacteristicPencilCoefficientResidue
import DimensionFourDependence.CharacteristicGaussPencilGeometry
import DimensionFourDependence.NativeProjectiveResidueIdeal

/-! # The characteristic pencil specializes at its own divisor over its own coefficient curve -/

namespace DimensionFourDependence

open MvPolynomial AlgebraicGeometry
open scoped TensorProduct

attribute [local instance] MvPolynomial.gradedAlgebra Algebra.TensorProduct.rightAlgebra

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

local instance characteristicPencilDivisorSpecializationIntegral : IsIntegral N :=
  extendedClosedGaussNormalizationScheme_isIntegral H I E hH e
noncomputable local instance characteristicPencilDivisorSpecializationAlgebra : Algebra E (N).functionField :=
  extendedClosedGaussOwnFunctionFieldAlgebra H I E hH e

/-- The original coordinate Hilbert-function and curve-degree
comparisons at an actual divisor, using the actual characteristic
pencil's relative coefficient curve and its constructed residue embedding. -/
noncomputable def NativeCharacteristicPencilDivisorDegreeComparison
    (hd : 0 < d) (hind : ¬ComponentsDependent H) (hGauss : gaussImageDimension H I = 1)
    (r : (N).functionField) (z : N) (hz : Order.coheight z = 1)
    (a : Fin 4) (ha : z ∈ U a) : Prop :=
  letI := extendedClosedGaussNormalization_divisor_stalk_isDVR H I E hH e z hz
  let C := pencilCoefficientCurveField (E := E)
    (nativeCharacteristicPencilValue H I E hH e hd hind hGauss r)
  letI := coefficientRestrictionResidueAlgebra
    (A := (N).presheaf.stalk z) (F := (N).functionField) C
  let J := (projectiveFieldPointIdeal
    (E := IsLocalRing.ResidueField (coefficientRestrictionValuationSubring
      (A := (N).presheaf.stalk z) (F := (N).functionField) C))
    (fun i => IsLocalRing.residue ((N).presheaf.stalk z)
      (nativeProjectiveCoordinateGerm H I E hH e z a ha i))).toIdeal
  (∀ n, projectiveHilbertFunction J n ≤
    projectiveHilbertFunction (projectiveFieldPointIdeal (E := C) w).toIdeal n) ∧
  (∀ D D' : ℕ, HasCurveHilbertDegree (projectiveFieldPointIdeal (E := C) w).toIdeal D →
    HasCurveHilbertDegree J D' → D' ≤ D)

/-- Instantiation uses the same original source coordinates and
actual local divisor. No coefficient valuation or residue compatibility
data are supplied to the characteristic pencil. -/
theorem actual_characteristic_pencil_divisor_degree_comparison
    (hd : 0 < d) (hind : ¬ComponentsDependent H) (hGauss : gaussImageDimension H I = 1)
    (r : (N).functionField) (z : N) (hz : Order.coheight z = 1)
    (a : Fin 4) (ha : z ∈ U a) :
    NativeCharacteristicPencilDivisorDegreeComparison H I E hH e hd hind hGauss r z hz a ha := by
  let C := pencilCoefficientCurveField (E := E)
    (nativeCharacteristicPencilValue H I E hH e hd hind hGauss r)
  constructor
  · exact fun n => native_normalization_divisor_projective_hilbert_bound H I E hH e z hz a ha C n
  · exact fun D D' hD => native_normalization_divisor_projective_curve_degree_bound
      H I E hH e z hz a ha C hD

variable [Module.Finite (closedGaussParameterField H I) E]
  (hd : 1 < d) (hind : ¬ComponentsDependent H) (hGauss : gaussImageDimension H I = 1)

/-- The same native characteristic factorization carries its
nonempty regular pencil geometry, transcendental parameter, actual
coefficient curve and one actual root divisor with algebraic coefficient
residue and the original-coordinate Hilbert and degree comparisons. -/
noncomputable def ActualCharacteristicGaussSpecializationData : Prop :=
  ∃ (cS cN : Fin 4 → E) (r : (N).functionField), cS ≠ 0 ∧ cN ≠ 0 ∧ r ≠ 0 ∧
    ∃ hroot : r ^ d = aeval w ((O) cS),
      CharacteristicNativeRulingRootFactorization H I E hH e
        (Nat.lt_trans Nat.zero_lt_one hd) hind hGauss cN r ∧
      HasActualGaussRootNumerator H I E e cN ∧
      CharacteristicGaussRootDivisorGeometry H I E hH e hd hind hGauss cS r hroot ∧
      Transcendental E (nativeCharacteristicPencilValue H I E hH e
        (Nat.lt_trans Nat.zero_lt_one hd) hind hGauss r) ∧
      Algebra.trdeg E (pencilCoefficientCurveField (E := E)
        (nativeCharacteristicPencilValue H I E hH e
          (Nat.lt_trans Nat.zero_lt_one hd) hind hGauss r)) = 1 ∧
      ∃ (a : Fin 4) (q : PrimeSpectrum (normalizationRing (T₀ a)))
        (_hq : q.asIdeal.height = 1) (hz : Order.coheight (z₀ a q) = 1),
        NativeCharacteristicPencilCoefficientResidueAlgebraic H I E hH e
          (Nat.lt_trans Nat.zero_lt_one hd) hind hGauss r (z₀ a q) hz ∧
        NativeCharacteristicPencilDivisorDegreeComparison H I E hH e
          (Nat.lt_trans Nat.zero_lt_one hd) hind hGauss r (z₀ a q) hz a
          (extendedClosedGaussNormalizationTensorChartPoint_mem_chart H I E hH e (finSuccEquiv' a) q)

/-- All coefficient and divisor-specialization data are constructed
from the same actual regular pencil; no new root or geometric branch is assumed. -/
theorem actual_characteristic_pencil_geometry_constructs_divisor_specialization
    (hdata : ActualCharacteristicGaussPencilData H I E hH e hd hind hGauss) :
    ActualCharacteristicGaussSpecializationData H I E hH e hd hind hGauss := by
  obtain ⟨cS, cN, r, hS, hN, hr, hroot, hfactor, hnumerator, _hL, _hnonconstant, hgeometry⟩ := hdata
  refine ⟨cS, cN, r, hS, hN, hr, hroot, hfactor, hnumerator, hgeometry, ?_, ?_, ?_⟩
  · exact actual_characteristic_pencil_value_transcendental H I E hH e
      hd hind hGauss cS cN r hr hroot hfactor
  · exact actual_characteristic_pencil_coefficient_curve_trdeg_one H I E hH e
      hd hind hGauss cS cN r hr hroot hfactor
  · obtain ⟨a, q, hq, hz, hres⟩ :=
      actual_characteristic_pencil_constructs_algebraic_coefficient_residue_divisor
        H I E hH e hd hind hGauss cS cN r hr hroot hfactor
    exact ⟨a, q, hq, hz, hres, actual_characteristic_pencil_divisor_degree_comparison
      H I E hH e (Nat.lt_trans Nat.zero_lt_one hd) hind hGauss r (z₀ a q) hz a
      (extendedClosedGaussNormalizationTensorChartPoint_mem_chart H I E hH e (finSuccEquiv' a) q)⟩

end DimensionFourDependence
