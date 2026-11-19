import DimensionFourDependence.LocalPencilZero
import DimensionFourDependence.NativePencilStalkConstants
import DimensionFourDependence.CharacteristicPencilNoCommonDivisor
import DimensionFourDependence.CharacteristicRootZeroDivisor

/-! # The characteristic pencil has a regular zero and a transcendental value -/

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

local instance characteristicPencilRegularZeroIntegral : IsIntegral N :=
  extendedClosedGaussNormalizationScheme_isIntegral H I E hH e
noncomputable local instance characteristicPencilRegularZeroAlgebra : Algebra E (N).functionField :=
  extendedClosedGaussOwnFunctionFieldAlgebra H I E hH e

/-- The actual ratio [rho:L_t] in the native normalized source field. -/
noncomputable def nativeCharacteristicPencilValue
    (hd : 0 < d) (hind : ¬ComponentsDependent H) (hGauss : gaussImageDimension H I = 1)
    (r : (N).functionField) : (N).functionField :=
  r / (∑ j, algebraMap E (N).functionField
    (extendedClosedGaussChosenRulingMatrix H I E hH hd hind hGauss 0 j) * w j)

variable [Module.Finite (closedGaussParameterField H I) E]

/-- At each actual root divisor, the characteristic pencil ratio
has a nonzero regular local representative with zero residue. The
specified coefficient field acts through the actual constant germs. -/
theorem actual_characteristic_pencil_value_has_regular_nonzero_zero
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
    ∃ f : (N).presheaf.stalk (z₀ a q), f ≠ 0 ∧
      f ∈ IsLocalRing.maximalIdeal ((N).presheaf.stalk (z₀ a q)) ∧
      algebraMap ((N).presheaf.stalk (z₀ a q)) (N).functionField f =
        nativeCharacteristicPencilValue H I E hH e (Nat.lt_trans Nat.zero_lt_one hd) hind hGauss r ∧
      Transcendental E (nativeCharacteristicPencilValue H I E hH e
        (Nat.lt_trans Nat.zero_lt_one hd) hind hGauss r) := by
  let z := z₀ a q
  let A := (N).presheaf.stalk z
  let ha := extendedClosedGaussNormalizationTensorChartPoint_mem_chart H I E hH e (finSuccEquiv' a) q
  let R := (N).presheaf.germ (U a) z ha
    (extendedClosedGaussHyperplaneGlobalCoefficient H I E hH e
      (extendedClosedGaussOutputLinearRootSection H I E hH e cS r (by omega) hroot) a)
  let L := extendedClosedGaussHyperplaneGlobalCoefficientGerm H I E hH e
    (extendedClosedGaussInputLinearSection H I E hH e
      (extendedClosedGaussChosenRulingMatrix H I E hH (by omega) hind hGauss 0)) a q
  let aEA : Algebra E A := extendedClosedGaussStalkCoefficientAlgebra H I E hH e z
  let tEAF : IsScalarTower E A (N).functionField :=
    extendedClosedGaussStalkCoefficientAlgebra_scalarTower H I E hH e z
  have hRv : algebraMap A (N).functionField R = r / w a := by
    rw [extendedClosedGaussHyperplaneGlobalCoefficient_germ_value,
      extendedClosedGaussOutputLinearRootSection_value]
  have hLv : algebraMap A (N).functionField L =
      (∑ j, algebraMap E (N).functionField
        (extendedClosedGaussChosenRulingMatrix H I E hH (by omega) hind hGauss 0 j) * w j) / w a := by
    unfold L extendedClosedGaussHyperplaneGlobalCoefficientGerm
    rw [extendedClosedGaussHyperplaneGlobalCoefficient_germ_value,
      extendedClosedGaussInputLinearSection_value]
  have hw : w a ≠ 0 := extendedClosedGaussNormalizationHyperplaneWeight_ne_zero H I E hH e a
  have hR : R ≠ 0 := by
    intro hz
    have he := hRv
    rw [hz, map_zero] at he
    exact div_ne_zero hr hw he.symm
  have hL : IsUnit L := IsLocalRing.notMem_maximalIdeal.mp
    (characteristic_root_and_tangent_plane_have_no_common_divisor
      H I E hH e hd hind hGauss cS cN r hroot hfactor a q hq hvan)
  have hLvalue : (∑ j, algebraMap E (N).functionField
      (extendedClosedGaussChosenRulingMatrix H I E hH (by omega) hind hGauss 0 j) * w j) ≠ 0 := by
    intro hz
    apply (hL.map (algebraMap A (N).functionField)).ne_zero
    rw [hLv, hz, zero_div]
  obtain ⟨f, hf, hzero, hvalue, ht⟩ :=
    local_unit_quotient_has_regular_nonzero_zero_and_transcendental_value
      (E := E) (F := (N).functionField) R L hR hvan hL
  have hquot : algebraMap A (N).functionField R / algebraMap A (N).functionField L =
      nativeCharacteristicPencilValue H I E hH e (Nat.lt_trans Nat.zero_lt_one hd) hind hGauss r := by
    rw [hRv, hLv, nativeCharacteristicPencilValue]
    field_simp [hw, hLvalue]
  rw [hquot] at hvalue ht
  exact ⟨f, hf, hzero, hvalue, ht⟩

/-- The original characteristic factorization supplies its own
root divisor, so the actual characteristic pencil value is transcendental
over its finite coefficient field without a separate parameter assumption. -/
theorem actual_characteristic_pencil_value_transcendental
    (hd : 1 < d) (hind : ¬ComponentsDependent H) (hGauss : gaussImageDimension H I = 1)
    (cS cN : Fin 4 → E) (r : (N).functionField) (hr : r ≠ 0)
    (hroot : r ^ d = aeval w ((O) cS))
    (hfactor : CharacteristicNativeRulingRootFactorization H I E hH e (by omega) hind hGauss cN r) :
    Transcendental E (nativeCharacteristicPencilValue H I E hH e
      (Nat.lt_trans Nat.zero_lt_one hd) hind hGauss r) := by
  obtain ⟨a, q, hq, _hcodim, hvan⟩ := actual_native_nonzero_root_section_has_zero_divisor
    H I E hH e hGauss (Nat.lt_trans Nat.zero_lt_one hd) cS r hr hroot
  obtain ⟨_f, _hf, _hzero, _hvalue, ht⟩ := actual_characteristic_pencil_value_has_regular_nonzero_zero
    H I E hH e hd hind hGauss cS cN r hr hroot hfactor a q hq hvan
  exact ht

end DimensionFourDependence
