import DimensionFourDependence.ExtendedSourceFormLocalIdeals
import DimensionFourDependence.NativeProportionalPowerFactorization

/-! # Characteristic factorization gives actual local component multiplicity -/

namespace DimensionFourDependence

open MvPolynomial AlgebraicGeometry

universe u

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

local notation "N" => extendedClosedGaussNormalizationScheme H I E hH e
local notation "U" a:max => extendedClosedGaussNormalizationChartOpen H I E hH e (finSuccEquiv' a)
local notation "w" => extendedClosedGaussNormalizationHyperplaneWeight H I E hH e
local notation "O" => extendedClosedGaussOutputLinearPolynomial H I E
local notation "ι" => extendedClosedGaussSourceCoefficientHom H I E

local instance characteristicRootMultiplicityIntegral : IsIntegral N :=
  extendedClosedGaussNormalizationScheme_isIntegral H I E hH e
noncomputable local instance characteristicRootMultiplicityAlgebra : Algebra E (N).functionField :=
  extendedClosedGaussOwnFunctionFieldAlgebra H I E hH e

/-- Formula (4.6) is an exact equality of regular original-frame
germs, not merely an equality in the normalization's function field. -/
theorem characteristic_root_factorization_regular_germ_identity
    (hd : 0 < d) (cS ν V W : Fin 4 → E) (r : (N).functionField)
    (hroot : r ^ d = aeval w ((O) cS))
    (hfactor : ∀ i, aeval w (MvPolynomial.map (ι) (H i)) = r ^ (d - 1) *
      (r * algebraMap E (N).functionField (V i) +
        (∑ j, algebraMap E (N).functionField (ν j) * w j) * algebraMap E (N).functionField (W i)))
    (z : N) (a : Fin 4) (ha : z ∈ U a) (i : Fin 4) :
    let R := (N).presheaf.germ (U a) z ha
      (extendedClosedGaussHyperplaneGlobalCoefficient H I E hH e
        (extendedClosedGaussOutputLinearRootSection H I E hH e cS r hd hroot) a)
    let L := (N).presheaf.germ (U a) z ha
      (extendedClosedGaussHyperplaneGlobalCoefficient H I E hH e
        (extendedClosedGaussInputLinearSection H I E hH e ν) a)
    let C := fun c : E => (N).presheaf.germ ⊤ z (by trivial)
      (extendedClosedGaussGlobalConstantHom H I E hH e c)
    extendedClosedGaussPolynomialCoefficientGerm H I E hH e (MvPolynomial.map (ι) (H i)) z a ha =
      R ^ (d - 1) * (R * C (V i) + L * C (W i)) := by
  dsimp only
  apply IsFractionRing.injective ((N).presheaf.stalk z) (N).functionField
  simp only [map_mul, map_add, map_pow]
  rw [extendedClosedGaussPolynomialCoefficientGerm_value H I E hH e _ ((hH i).map (ι)) z a ha,
    extendedClosedGaussHyperplaneGlobalCoefficient_germ_value,
    extendedClosedGaussHyperplaneGlobalCoefficient_germ_value,
    extendedClosedGaussOutputLinearRootSection_value,
    extendedClosedGaussInputLinearSection_value,
    extendedClosedGaussGlobalConstantHom_germ_value,
    extendedClosedGaussGlobalConstantHom_germ_value, hfactor i]
  have hw : w a ≠ 0 := extendedClosedGaussNormalizationHyperplaneWeight_ne_zero H I E hH e a
  have hdegree : w a ^ d = w a ^ (d - 1) * w a := by
    rw [← pow_succ]
    congr 1
    omega
  rw [div_pow, hdegree]
  field_simp [hw]
  <;> ring

/-- At every zero of the actual regular root section, all four
original output germs belong to the (d-1)-st maximal-ideal power. -/
theorem characteristic_root_zero_original_component_multiplicity
    (hd : 0 < d) (cS ν V W : Fin 4 → E) (r : (N).functionField)
    (hroot : r ^ d = aeval w ((O) cS))
    (hfactor : ∀ i, aeval w (MvPolynomial.map (ι) (H i)) = r ^ (d - 1) *
      (r * algebraMap E (N).functionField (V i) +
        (∑ j, algebraMap E (N).functionField (ν j) * w j) * algebraMap E (N).functionField (W i)))
    (z : N) (a : Fin 4) (ha : z ∈ U a)
    (hvan : (N).presheaf.germ (U a) z ha
      (extendedClosedGaussHyperplaneGlobalCoefficient H I E hH e
        (extendedClosedGaussOutputLinearRootSection H I E hH e cS r hd hroot) a) ∈
      IsLocalRing.maximalIdeal ((N).presheaf.stalk z)) :
    ∀ i, extendedClosedGaussPolynomialCoefficientGerm H I E hH e
      (MvPolynomial.map (ι) (H i)) z a ha ∈ IsLocalRing.maximalIdeal ((N).presheaf.stalk z) ^ (d - 1) := by
  intro i
  rw [characteristic_root_factorization_regular_germ_identity H I E hH e hd cS ν V W r hroot hfactor z a ha i]
  exact (IsLocalRing.maximalIdeal ((N).presheaf.stalk z) ^ (d - 1)).mul_mem_right _
    (Ideal.pow_mem_pow hvan (d - 1))

end DimensionFourDependence
