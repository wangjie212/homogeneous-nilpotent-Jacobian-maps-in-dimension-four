import DimensionFourDependence.CharacteristicPencilNonproportional
import DimensionFourDependence.IndependentNormalCharacteristicRoot

/-! # The actual characteristic root data construct their regular pencil geometry -/

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
  [Module.Finite (closedGaussParameterField H I) E]
  {d : ℕ} (hH : IsHomogMap H d)
  (e : RatFunc K ≃ₐ[K] closedGaussParameterField H I)
  (hd : 1 < d) (hind : ¬ComponentsDependent H) (hGauss : gaussImageDimension H I = 1)

local notation "C₀" => closedGaussParameterField H I
local notation "T₀" a:max => projectiveCoordinateChartAlgebra (C := C₀)
  (rationalCoordinate (K := K) (n := 4)) ((finSuccEquiv' a).symm none) ⊗[C₀] E
local notation "N" => extendedClosedGaussNormalizationScheme H I E hH e
local notation "U" a:max => extendedClosedGaussNormalizationChartOpen H I E hH e (finSuccEquiv' a)
local notation "w" => extendedClosedGaussNormalizationHyperplaneWeight H I E hH e
local notation "O" => extendedClosedGaussOutputLinearPolynomial H I E
local notation "z₀" a:max q:max => extendedClosedGaussNormalizationTensorChartPoint H I E hH e (finSuccEquiv' a) q
local notation "m" => extendedClosedGaussNormalizationSourceMorphism H I E hH e
local notation "ν₀" => extendedClosedGaussChosenRulingMatrix H I E hH (Nat.lt_trans Nat.zero_lt_one hd) hind hGauss 0
local notation "Lₜ" => ∑ j, algebraMap E (N).functionField ((ν₀) j) * w j

local instance characteristicGaussPencilGeometryIntegral : IsIntegral N :=
  extendedClosedGaussNormalizationScheme_isIntegral H I E hH e
noncomputable local instance characteristicGaussPencilGeometryAlgebra : Algebra E (N).functionField :=
  extendedClosedGaussOwnFunctionFieldAlgebra H I E hH e

/-- Every divisor of the actual root avoids the tangent-plane divisor
and has no original source-divisor image; at least one such divisor exists. -/
noncomputable def CharacteristicGaussRootDivisorGeometry
    (cS : Fin 4 → E) (r : (N).functionField) (hroot : r ^ d = aeval w ((O) cS)) : Prop :=
  let rootZero := fun (a : Fin 4) (q : PrimeSpectrum (normalizationRing (T₀ a))) =>
    (N).presheaf.germ (U a) (z₀ a q)
      (extendedClosedGaussNormalizationTensorChartPoint_mem_chart H I E hH e (finSuccEquiv' a) q)
      (extendedClosedGaussHyperplaneGlobalCoefficient H I E hH e
        (extendedClosedGaussOutputLinearRootSection H I E hH e cS r (Nat.lt_trans Nat.zero_lt_one hd) hroot) a) ∈
      IsLocalRing.maximalIdeal ((N).presheaf.stalk (z₀ a q))
  (∀ (a : Fin 4) (q : PrimeSpectrum (normalizationRing (T₀ a))), q.asIdeal.height = 1 → rootZero a q →
      Order.coheight ((m) (z₀ a q)) ≠ 1 ∧
      extendedClosedGaussHyperplaneGlobalCoefficientGerm H I E hH e
        (extendedClosedGaussInputLinearSection H I E hH e (ν₀)) a q ∉
          IsLocalRing.maximalIdeal ((N).presheaf.stalk (z₀ a q))) ∧
    ∃ (a : Fin 4) (q : PrimeSpectrum (normalizationRing (T₀ a))), q.asIdeal.height = 1 ∧
      Order.coheight (z₀ a q) = 1 ∧ rootZero a q

/-- The same native characteristic root, numerator and factorization
carry an actual regular pencil with a nonempty root divisor, no common
divisor, and a ratio outside the specified coefficient-field image. -/
noncomputable def ActualCharacteristicGaussPencilData : Prop :=
  ∃ (cS cN : Fin 4 → E) (r : (N).functionField), cS ≠ 0 ∧ cN ≠ 0 ∧ r ≠ 0 ∧
    ∃ hroot : r ^ d = aeval w ((O) cS),
      CharacteristicNativeRulingRootFactorization H I E hH e (Nat.lt_trans Nat.zero_lt_one hd) hind hGauss cN r ∧
      HasActualGaussRootNumerator H I E e cN ∧ (Lₜ) ≠ 0 ∧
      (∀ b : E, r / (Lₜ) ≠ algebraMap E (N).functionField b) ∧
      CharacteristicGaussRootDivisorGeometry H I E hH e hd hind hGauss cS r hroot

/-- All of this actual pencil geometry follows from the original
characteristic root data; no zero divisor, local multiplicity, source
codimension or absence of common components is supplied. -/
theorem actual_characteristic_root_data_constructs_regular_pencil_geometry
    (hdata : ActualCharacteristicGaussRootData H I E hH e (Nat.lt_trans Nat.zero_lt_one hd) hind hGauss) :
    ActualCharacteristicGaussPencilData H I E hH e hd hind hGauss := by
  obtain ⟨cS, cM, cN, r, hS, _hM, hN, hr, hroot, _hm, hformula, _hMN, _hSN, hfactor, hnumerator⟩ := hdata
  have hL : (Lₜ) ≠ 0 := by
    intro hz
    apply hr
    rw [hformula, hz, mul_zero, zero_div]
  refine ⟨cS, cN, r, hS, hN, hr, hroot, hfactor, hnumerator, hL, ?_, ?_⟩
  · exact fun b => characteristic_root_tangent_plane_ratio_not_in_coefficient_image
      H I E hH e hd hind hGauss cS cN r hr hroot hfactor hL b
  · constructor
    · intro a q hq hvan
      exact ⟨characteristic_native_root_zero_source_coheight_ne_one H I E hH e hd hind hGauss
          cS cN r hroot hfactor (z₀ a q) a
          (extendedClosedGaussNormalizationTensorChartPoint_mem_chart H I E hH e (finSuccEquiv' a) q) hvan,
        characteristic_root_and_tangent_plane_have_no_common_divisor H I E hH e hd hind hGauss
          cS cN r hroot hfactor a q hq hvan⟩
    · exact actual_native_nonzero_root_section_has_zero_divisor H I E hH e hGauss
        (Nat.lt_trans Nat.zero_lt_one hd) cS r hr hroot

end DimensionFourDependence
