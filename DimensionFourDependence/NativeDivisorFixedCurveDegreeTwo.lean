import DimensionFourDependence.OriginalRootFixedCurveDegreeDescent
import DimensionFourDependence.NativeTensorDivisorResidue
import DimensionFourDependence.ProjectiveHilbertAlgebraTransport
import DimensionFourDependence.CharacteristicPencilSpecializedDegreeTwo

/-! # The actual root divisor's positive source-curve degree descends to the original constants -/

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
local notation "x₀" a:max q:max => fun i : Fin 4 => (finSuccEquiv' a i).elim 1 (y₀ a q)
local notation "N" => extendedClosedGaussNormalizationScheme H I E hH e
local notation "w" => extendedClosedGaussNormalizationHyperplaneWeight H I E hH e
local notation "O" => extendedClosedGaussOutputLinearPolynomial H I E
local notation "z₀" a:max q:max => extendedClosedGaussNormalizationTensorChartPoint H I E hH e (finSuccEquiv' a) q
local notation "ha₀" a:max q:max => extendedClosedGaussNormalizationTensorChartPoint_mem_chart H I E hH e (finSuccEquiv' a) q
local notation "U₀" a:max => extendedClosedGaussNormalizationChartOpen H I E hH e (finSuccEquiv' a)
local notation "A₀" a:max q:max => (N).presheaf.stalk (z₀ a q)

local instance nativeDivisorFixedCurveDegreeTwoIntegral : IsIntegral N :=
  extendedClosedGaussNormalizationScheme_isIntegral H I E hH e
noncomputable local instance nativeDivisorFixedCurveDegreeTwoAlgebra : Algebra E (N).functionField :=
  extendedClosedGaussOwnFunctionFieldAlgebra H I E hH e

/-- The actual residue comparison retains all four original projective
coordinates, including the unit coordinate of the original chart. -/
theorem nativeTensorDivisorResidueAlgEquiv_projective_coordinate
    (a : Fin 4) (q : PrimeSpectrum (normalizationRing (T₀ a))) (i : Fin 4) :
    letI := extendedClosedGaussStalkCoefficientAlgebra H I E hH e (z₀ a q)
    nativeTensorDivisorResidueAlgEquiv H I E hH e a q
      (IsLocalRing.residue (A₀ a q)
        (nativeProjectiveCoordinateGerm H I E hH e (z₀ a q) a (ha₀ a q) i)) = (x₀ a q) i := by
  letI := extendedClosedGaussStalkCoefficientAlgebra H I E hH e (z₀ a q)
  let φ := nativeTensorDivisorResidueAlgEquiv H I E hH e a q
  let z := fun j => φ (IsLocalRing.residue (A₀ a q)
    (nativeProjectiveCoordinateGerm H I E hH e (z₀ a q) a (ha₀ a q) j))
  have hf : z a = 1 := by
    exact (congrArg (fun t => φ (IsLocalRing.residue (A₀ a q) t))
      (nativeProjectiveCoordinateGerm_frame H I E hH e (z₀ a q) a (ha₀ a q))).trans
        ((congrArg φ (map_one (IsLocalRing.residue (A₀ a q)))).trans (map_one φ))
  exact congrFun (restored_projective_coordinates_eq_of_frame_and_affine
    (finSuccEquiv' a) z (y₀ a q) a (finSuccEquiv'_symm_none a) hf
    (nativeTensorDivisorResidueAlgEquiv_coordinate H I E hH e a q)) i

/-- The positive degree at most two constructed over the actual
restricted coefficient residue is the degree of the same fixed
source-coordinate curve over the original algebraically closed constants.
All coefficient actions and residue-field identifications are constructed. -/
theorem actual_characteristic_root_divisor_fixed_source_degree_at_most_two
    [IsAlgClosed K] [Module.Finite C₀ E]
    (hd : 1 < d) (hind : ¬ComponentsDependent H) (hGauss : gaussImageDimension H I = 1)
    (cS cN : Fin 4 → E) (r : (N).functionField)
    (hroot : r ^ d = aeval (w) ((O) cS))
    (hfactor : CharacteristicNativeRulingRootFactorization H I E hH e
      (Nat.lt_trans Nat.zero_lt_one hd) hind hGauss cN r)
    (a : Fin 4) (q : PrimeSpectrum (normalizationRing (T₀ a))) (hq : q.asIdeal.height = 1)
    (hz : Order.coheight (z₀ a q) = 1)
    (hvan : (N).presheaf.germ (U₀ a) (z₀ a q) (ha₀ a q)
      (extendedClosedGaussHyperplaneGlobalCoefficient H I E hH e
        (extendedClosedGaussOutputLinearRootSection H I E hH e cS r
          (Nat.lt_trans Nat.zero_lt_one hd) hroot) a) ∈
      IsLocalRing.maximalIdeal (A₀ a q))
    (hres : NativeCharacteristicPencilCoefficientResidueAlgebraic H I E hH e
      (Nat.lt_trans Nat.zero_lt_one hd) hind hGauss r (z₀ a q) hz)
    (hdegree : NativeCharacteristicPencilDivisorPositiveDegreeTwo H I E hH e hd hind hGauss r a q hz) :
    ∃ D : ℕ, D ≤ 2 ∧ HasCurveHilbertDegree
      (projectiveFieldPointIdeal (E := K) (x₀ a q)).toIdeal D := by
  letI := extendedClosedGaussNormalization_divisor_stalk_isDVR H I E hH e (z₀ a q) hz
  letI := extendedClosedGaussStalkCoefficientAlgebra H I E hH e (z₀ a q)
  letI := extendedClosedGaussStalkCoefficientAlgebra_scalarTower H I E hH e (z₀ a q)
  let P := pencilCoefficientCurveField (E := E)
    (nativeCharacteristicPencilValue H I E hH e (Nat.lt_trans Nat.zero_lt_one hd) hind hGauss r)
  letI := pencilCoefficientCurveField_scalarTower (E := E)
    (nativeCharacteristicPencilValue H I E hH e (Nat.lt_trans Nat.zero_lt_one hd) hind hGauss r)
  let V := coefficientRestrictionValuationSubring (A := A₀ a q) (F := (N).functionField) P
  let C := IsLocalRing.ResidueField V
  letI := coefficientRestrictionConstantAlgebra (A := A₀ a q) (F := (N).functionField) P E
  letI : Algebra.IsAlgebraic E C := hres
  letI := coefficientRestrictionResidueAlgebra (A := A₀ a q) (F := (N).functionField) P
  letI := coefficientRestrictionResidueAlgebra_constant_scalarTower
    (E := E) (A := A₀ a q) (F := (N).functionField) P
  let φ := nativeTensorDivisorResidueAlgEquiv H I E hH e a q
  let aCF := transportedCoefficientAlgebra (C := C) φ
  have hTower : letI : Algebra C (F₀ a q) := aCF
      letI : SMul C (F₀ a q) := aCF.toSMul
      IsScalarTower E C (F₀ a q) :=
    transportedCoefficientAlgebra_scalarTower (C := C) φ
  have hh (n : ℕ) := actual_characteristic_root_fixed_source_hilbert_eq_algebraic_coefficients
    H I E hH e hd hind hGauss cS cN r hroot hfactor a q hq hvan C aCF hTower n
  letI : Algebra C (F₀ a q) := aCF
  letI : SMul C (F₀ a q) := aCF.toSMul
  have hx : (fun i => φ (IsLocalRing.residue (A₀ a q)
      (nativeProjectiveCoordinateGerm H I E hH e (z₀ a q) a (ha₀ a q) i))) = (x₀ a q) :=
    funext (nativeTensorDivisorResidueAlgEquiv_projective_coordinate H I E hH e a q)
  obtain ⟨D, hD2, hD⟩ := hdegree
  have hDC := projective_curve_degree_of_transported_coordinates (C := C) φ
    (fun i => IsLocalRing.residue (A₀ a q)
      (nativeProjectiveCoordinateGerm H I E hH e (z₀ a q) a (ha₀ a q) i))
    (x₀ a q) hx hD
  refine ⟨D, hD2, ?_⟩
  simpa only [HasCurveHilbertDegree, hh] using hDC

end DimensionFourDependence
