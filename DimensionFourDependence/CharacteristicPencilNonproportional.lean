import DimensionFourDependence.CharacteristicRootZeroDivisor
import DimensionFourDependence.CharacteristicPencilNoCommonDivisor

/-! # The characteristic root is not a constant multiple of its tangent plane -/

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

local notation "N" => extendedClosedGaussNormalizationScheme H I E hH e
local notation "U" a:max => extendedClosedGaussNormalizationChartOpen H I E hH e (finSuccEquiv' a)
local notation "w" => extendedClosedGaussNormalizationHyperplaneWeight H I E hH e
local notation "O" => extendedClosedGaussOutputLinearPolynomial H I E

local instance characteristicPencilNonproportionalIntegral : IsIntegral N :=
  extendedClosedGaussNormalizationScheme_isIntegral H I E hH e
noncomputable local instance characteristicPencilNonproportionalAlgebra : Algebra E (N).functionField :=
  extendedClosedGaussOwnFunctionFieldAlgebra H I E hH e

/-- The actual root and tangent-plane sections are not proportional
over the specified coefficient field. A constructed root zero would
otherwise be a common divisor of their actual regular sections. -/
theorem characteristic_root_not_constant_multiple_of_chosen_tangent_plane
    (hd : 1 < d) (hind : ¬ComponentsDependent H) (hGauss : gaussImageDimension H I = 1)
    (cS cN : Fin 4 → E) (r : (N).functionField) (hr : r ≠ 0)
    (hroot : r ^ d = aeval w ((O) cS))
    (hfactor : CharacteristicNativeRulingRootFactorization H I E hH e (by omega) hind hGauss cN r)
    (ℓ : E) : r ≠ algebraMap E (N).functionField ℓ *
      (∑ j, algebraMap E (N).functionField
        (extendedClosedGaussChosenRulingMatrix H I E hH (by omega) hind hGauss 0 j) * w j) := by
  intro hprop
  have hℓ : ℓ ≠ 0 := by
    intro hz
    apply hr
    rw [hprop, hz, map_zero, zero_mul]
  obtain ⟨a, q, hq, _hcodim, hvan⟩ := actual_native_nonzero_root_section_has_zero_divisor
    H I E hH e hGauss (by omega) cS r hr hroot
  let z := extendedClosedGaussNormalizationTensorChartPoint H I E hH e (finSuccEquiv' a) q
  let ha := extendedClosedGaussNormalizationTensorChartPoint_mem_chart H I E hH e (finSuccEquiv' a) q
  let ν := extendedClosedGaussChosenRulingMatrix H I E hH (by omega) hind hGauss 0
  let R := (N).presheaf.germ (U a) z ha
    (extendedClosedGaussHyperplaneGlobalCoefficient H I E hH e
      (extendedClosedGaussOutputLinearRootSection H I E hH e cS r (by omega) hroot) a)
  let L := extendedClosedGaussHyperplaneGlobalCoefficientGerm H I E hH e
    (extendedClosedGaussInputLinearSection H I E hH e ν) a q
  let C := (N).presheaf.germ ⊤ z (by trivial) (extendedClosedGaussGlobalConstantHom H I E hH e ℓ⁻¹)
  have hlinear : L = C * R := by
    dsimp only [L, C, R, extendedClosedGaussHyperplaneGlobalCoefficientGerm]
    apply IsFractionRing.injective ((N).presheaf.stalk z) (N).functionField
    rw [map_mul, extendedClosedGaussHyperplaneGlobalCoefficient_germ_value,
      extendedClosedGaussHyperplaneGlobalCoefficient_germ_value,
      extendedClosedGaussInputLinearSection_value, extendedClosedGaussOutputLinearRootSection_value,
      extendedClosedGaussGlobalConstantHom_germ_value, map_inv₀, hprop]
    have hℓF : algebraMap E (N).functionField ℓ ≠ 0 := (map_ne_zero _).mpr hℓ
    field_simp [hℓF]
    rfl
  have hL : L ∈ IsLocalRing.maximalIdeal ((N).presheaf.stalk z) := by
    rw [hlinear]
    exact (IsLocalRing.maximalIdeal ((N).presheaf.stalk z)).mul_mem_left C hvan
  exact characteristic_root_and_tangent_plane_have_no_common_divisor H I E hH e hd hind hGauss
    cS cN r hroot hfactor a q hq hvan hL

/-- Where the actual tangent-plane value is nonzero, its ratio with
the root takes no value in the specified constant-field image. -/
theorem characteristic_root_tangent_plane_ratio_not_in_coefficient_image
    (hd : 1 < d) (hind : ¬ComponentsDependent H) (hGauss : gaussImageDimension H I = 1)
    (cS cN : Fin 4 → E) (r : (N).functionField) (hr : r ≠ 0)
    (hroot : r ^ d = aeval w ((O) cS))
    (hfactor : CharacteristicNativeRulingRootFactorization H I E hH e (by omega) hind hGauss cN r)
    (hL : (∑ j, algebraMap E (N).functionField
      (extendedClosedGaussChosenRulingMatrix H I E hH (by omega) hind hGauss 0 j) * w j) ≠ 0)
    (ℓ : E) : r / (∑ j, algebraMap E (N).functionField
      (extendedClosedGaussChosenRulingMatrix H I E hH (by omega) hind hGauss 0 j) * w j) ≠
        algebraMap E (N).functionField ℓ := by
  intro he
  exact characteristic_root_not_constant_multiple_of_chosen_tangent_plane
    H I E hH e hd hind hGauss cS cN r hr hroot hfactor ℓ ((div_eq_iff hL).mp he)

end DimensionFourDependence
