import DimensionFourDependence.CharacteristicPencilRegularZero
import DimensionFourDependence.RegularPencilCoefficientResidue
import DimensionFourDependence.NativeDivisorCoordinateHilbert

/-! # The actual characteristic pencil constructs its coefficient curve and algebraic residue -/

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

local instance characteristicPencilCoefficientResidueIntegral : IsIntegral N :=
  extendedClosedGaussNormalizationScheme_isIntegral H I E hH e
noncomputable local instance characteristicPencilCoefficientResidueAlgebra : Algebra E (N).functionField :=
  extendedClosedGaussOwnFunctionFieldAlgebra H I E hH e

/-- The algebraic-residue assertion at one actual divisor, using
its own stalk valuation, actual constant germs and the full relative
coefficient closure of the original characteristic pencil value. -/
noncomputable def NativeCharacteristicPencilCoefficientResidueAlgebraic
    (hd : 0 < d) (hind : ¬ComponentsDependent H) (hGauss : gaussImageDimension H I = 1)
    (r : (N).functionField) (z : N) (hz : Order.coheight z = 1) : Prop :=
  letI := extendedClosedGaussNormalization_divisor_stalk_isDVR H I E hH e z hz
  letI := extendedClosedGaussStalkCoefficientAlgebra H I E hH e z
  letI := extendedClosedGaussStalkCoefficientAlgebra_scalarTower H I E hH e z
  let t := nativeCharacteristicPencilValue H I E hH e hd hind hGauss r
  let C := pencilCoefficientCurveField (E := E) t
  letI := pencilCoefficientCurveField_scalarTower (E := E) t
  letI := coefficientRestrictionConstantAlgebra
    (A := (N).presheaf.stalk z) (F := (N).functionField) C E
  Algebra.IsAlgebraic E (IsLocalRing.ResidueField
    (coefficientRestrictionValuationSubring (A := (N).presheaf.stalk z) (F := (N).functionField) C))

variable [Module.Finite (closedGaussParameterField H I) E]

/-- The actual characteristic factorization makes the full relative
pencil coefficient closure an actual one-dimensional field. -/
theorem actual_characteristic_pencil_coefficient_curve_trdeg_one
    (hd : 1 < d) (hind : ¬ComponentsDependent H) (hGauss : gaussImageDimension H I = 1)
    (cS cN : Fin 4 → E) (r : (N).functionField) (hr : r ≠ 0)
    (hroot : r ^ d = aeval w ((O) cS))
    (hfactor : CharacteristicNativeRulingRootFactorization H I E hH e (by omega) hind hGauss cN r) :
    Algebra.trdeg E (pencilCoefficientCurveField (E := E)
      (nativeCharacteristicPencilValue H I E hH e (Nat.lt_trans Nat.zero_lt_one hd) hind hGauss r)) = 1 :=
  pencilCoefficientCurveField_trdeg_one _
    (actual_characteristic_pencil_value_transcendental H I E hH e hd hind hGauss cS cN r hr hroot hfactor)

/-- At every actual root divisor the same pencil constructs its
coefficient valuation and algebraic residue field; neither parameter
transcendence nor residue algebraicity is supplied. -/
theorem actual_characteristic_pencil_zero_coefficient_residue_isAlgebraic
    (hd : 1 < d) (hind : ¬ComponentsDependent H) (hGauss : gaussImageDimension H I = 1)
    (cS cN : Fin 4 → E) (r : (N).functionField) (hr : r ≠ 0)
    (hroot : r ^ d = aeval w ((O) cS))
    (hfactor : CharacteristicNativeRulingRootFactorization H I E hH e (by omega) hind hGauss cN r)
    (a : Fin 4) (q : PrimeSpectrum (normalizationRing (T₀ a))) (hq : q.asIdeal.height = 1)
    (hvan : (N).presheaf.germ (U a) (z₀ a q)
      (extendedClosedGaussNormalizationTensorChartPoint_mem_chart H I E hH e (finSuccEquiv' a) q)
      (extendedClosedGaussHyperplaneGlobalCoefficient H I E hH e
        (extendedClosedGaussOutputLinearRootSection H I E hH e cS r (by omega) hroot) a) ∈
      IsLocalRing.maximalIdeal ((N).presheaf.stalk (z₀ a q))) :
    NativeCharacteristicPencilCoefficientResidueAlgebraic H I E hH e
      (Nat.lt_trans Nat.zero_lt_one hd) hind hGauss r (z₀ a q)
      ((extendedClosedGaussNormalizationTensorChartPoint_coheight_eq_height
        H I E hH e (finSuccEquiv' a) q).trans hq) := by
  obtain ⟨f, hf, hzero, hvalue, _ht⟩ := actual_characteristic_pencil_value_has_regular_nonzero_zero
    H I E hH e hd hind hGauss cS cN r hr hroot hfactor a q hq hvan
  let z := z₀ a q
  have hz : Order.coheight z = 1 :=
    (extendedClosedGaussNormalizationTensorChartPoint_coheight_eq_height
      H I E hH e (finSuccEquiv' a) q).trans hq
  letI := extendedClosedGaussNormalization_divisor_stalk_isDVR H I E hH e z hz
  letI := extendedClosedGaussStalkCoefficientAlgebra H I E hH e z
  letI := extendedClosedGaussStalkCoefficientAlgebra_scalarTower H I E hH e z
  exact regular_pencil_coefficient_curve_residue_isAlgebraic
    (E := E) (A := (N).presheaf.stalk z) (F := (N).functionField)
    (nativeCharacteristicPencilValue H I E hH e (Nat.lt_trans Nat.zero_lt_one hd) hind hGauss r)
    f hf hzero hvalue

/-- The characteristic root constructs an actual divisor where
its full coefficient curve has algebraic residue over the original
extended Gauss constants. The divisor is not assumed. -/
theorem actual_characteristic_pencil_constructs_algebraic_coefficient_residue_divisor
    (hd : 1 < d) (hind : ¬ComponentsDependent H) (hGauss : gaussImageDimension H I = 1)
    (cS cN : Fin 4 → E) (r : (N).functionField) (hr : r ≠ 0)
    (hroot : r ^ d = aeval w ((O) cS))
    (hfactor : CharacteristicNativeRulingRootFactorization H I E hH e (by omega) hind hGauss cN r) :
    ∃ (a : Fin 4) (q : PrimeSpectrum (normalizationRing (T₀ a)))
      (_hq : q.asIdeal.height = 1) (hz : Order.coheight (z₀ a q) = 1),
      NativeCharacteristicPencilCoefficientResidueAlgebraic H I E hH e
        (Nat.lt_trans Nat.zero_lt_one hd) hind hGauss r (z₀ a q) hz := by
  obtain ⟨a, q, hq, hz, hvan⟩ := actual_native_nonzero_root_section_has_zero_divisor
    H I E hH e hGauss (Nat.lt_trans Nat.zero_lt_one hd) cS r hr hroot
  exact ⟨a, q, hq, hz, actual_characteristic_pencil_zero_coefficient_residue_isAlgebraic
    H I E hH e hd hind hGauss cS cN r hr hroot hfactor a q hq hvan⟩

end DimensionFourDependence
