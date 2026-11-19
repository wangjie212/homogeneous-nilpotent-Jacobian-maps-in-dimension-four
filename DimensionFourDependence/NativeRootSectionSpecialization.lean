import DimensionFourDependence.ExtendedRationalRootMultiplicity
import DimensionFourDependence.NativePolynomialGermPointEquations
import DimensionFourDependence.ExtendedNativeLinearCombinations

/-! # Root-section zeros preserve their actual branch specializations and frame changes -/

namespace DimensionFourDependence

open MvPolynomial AlgebraicGeometry Topology

attribute [local instance] MvPolynomial.gradedAlgebra

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
local notation "f" => extendedClosedGaussNormalizationProjectiveMap H I E hH e
local notation "U" a:max => extendedClosedGaussNormalizationChartOpen H I E hH e (finSuccEquiv' a)
local notation "w" => extendedClosedGaussNormalizationHyperplaneWeight H I E hH e
local notation "O" => extendedClosedGaussOutputLinearPolynomial H I E
local notation "R₀" c:max r:max hd:max hroot:max =>
  extendedClosedGaussOutputLinearRootSection H I E hH e c r hd hroot

local instance nativeRootSectionSpecializationIntegral : IsIntegral N :=
  extendedClosedGaussNormalizationScheme_isIntegral H I E hH e
noncomputable local instance nativeRootSectionSpecializationAlgebra : Algebra E (N).functionField :=
  extendedClosedGaussOwnFunctionFieldAlgebra H I E hH e

/-- The actual regular root germ has exactly the prescribed d-th
power in every original projective chart at every native point. -/
theorem native_output_linear_root_germ_power
    (hd : 0 < d) (c : Fin 4 → E) (r : (N).functionField)
    (hroot : r ^ d = aeval (w) ((O) c))
    (z : N) (a : Fin 4) (ha : z ∈ U a) :
    ((N).presheaf.germ (U a) z ha
      (extendedClosedGaussHyperplaneGlobalCoefficient H I E hH e (R₀ c r hd hroot) a)) ^ d =
        extendedClosedGaussPolynomialCoefficientGerm H I E hH e ((O) c) z a ha := by
  apply IsFractionRing.injective ((N).presheaf.stalk z) (N).functionField
  rw [map_pow, extendedClosedGaussHyperplaneGlobalCoefficient_germ_value,
    extendedClosedGaussOutputLinearRootSection_value,
    extendedClosedGaussPolynomialCoefficientGerm_value H I E hH e ((O) c)
      (extendedClosedGaussOutputLinearPolynomial_homogeneous H I E hH c),
    div_pow, hroot]

/-- Vanishing of the regular root section is equivalent to its
original output-linear homogeneous equation at the actual source image.
This description is independent of the chosen source frame. -/
theorem native_output_linear_root_zero_iff_source_equation
    (hd : 0 < d) (c : Fin 4 → E) (r : (N).functionField)
    (hroot : r ^ d = aeval (w) ((O) c))
    (z : N) (a : Fin 4) (ha : z ∈ U a) :
    (N).presheaf.germ (U a) z ha
        (extendedClosedGaussHyperplaneGlobalCoefficient H I E hH e (R₀ c r hd hroot) a) ∈
          IsLocalRing.maximalIdeal ((N).presheaf.stalk z) ↔
      (O) c ∈ ((f) z).asHomogeneousIdeal := by
  rw [← native_polynomial_germ_mem_maximal_iff_projective_equation H I E hH e
    ((O) c) (extendedClosedGaussOutputLinearPolynomial_homogeneous H I E hH c) z a ha,
    ← native_output_linear_root_germ_power H I E hH e hd c r hroot z a ha]
  have hp : (IsLocalRing.maximalIdeal ((N).presheaf.stalk z)).IsPrime := inferInstance
  exact (hp.pow_mem_iff_mem d hd).symm

/-- A zero on a given root-divisor branch stays a zero at every
specialization of that branch, in any original chart containing the
specialized point. Both the point and the new chart are retained. -/
theorem native_output_linear_root_zero_specializes
    (hd : 0 < d) (c : Fin 4 → E) (r : (N).functionField)
    (hroot : r ^ d = aeval (w) ((O) c))
    (x z : N) (hxz : x ⤳ z)
    (a : Fin 4) (hx : x ∈ U a) (b : Fin 4) (hz : z ∈ U b)
    (hzero : (N).presheaf.germ (U a) x hx
      (extendedClosedGaussHyperplaneGlobalCoefficient H I E hH e (R₀ c r hd hroot) a) ∈
        IsLocalRing.maximalIdeal ((N).presheaf.stalk x)) :
    (N).presheaf.germ (U b) z hz
      (extendedClosedGaussHyperplaneGlobalCoefficient H I E hH e (R₀ c r hd hroot) b) ∈
        IsLocalRing.maximalIdeal ((N).presheaf.stalk z) := by
  apply (native_output_linear_root_zero_iff_source_equation H I E hH e hd c r hroot z b hz).mpr
  have hS := (native_output_linear_root_zero_iff_source_equation H I E hH e hd c r hroot x a hx).mp hzero
  have hxS : (f) x ∈ ProjectiveSpectrum.zeroLocus (homogeneousSubmodule (Fin 4) E) {(O) c} :=
    Set.singleton_subset_iff.mpr hS
  have hzS := (hxz.map (f).continuous).mem_closed
    (ProjectiveSpectrum.isClosed_zeroLocus (homogeneousSubmodule (Fin 4) E) {(O) c}) hxS
  exact hzS (Set.mem_singleton ((O) c))

/-- The actual input hyperplane section and the original linear
polynomial have precisely the same regular germ in every native chart. -/
theorem native_input_linear_section_germ_eq_polynomial
    (ν : Fin 4 → E) (z : N) (a : Fin 4) (ha : z ∈ U a) :
    (N).presheaf.germ (U a) z ha
        (extendedClosedGaussHyperplaneGlobalCoefficient H I E hH e
          (extendedClosedGaussInputLinearSection H I E hH e ν) a) =
      extendedClosedGaussPolynomialCoefficientGerm H I E hH e (linearFormPolynomial ν) z a ha := by
  apply IsFractionRing.injective ((N).presheaf.stalk z) (N).functionField
  rw [extendedClosedGaussHyperplaneGlobalCoefficient_germ_value,
    extendedClosedGaussInputLinearSection_value,
    extendedClosedGaussPolynomialCoefficientGerm_value H I E hH e
      (linearFormPolynomial ν) (extendedClosedGaussInputLinearPolynomial_homogeneous E ν), pow_one]
  simp only [linearFormPolynomial, map_sum, map_mul, aeval_C, aeval_X]

/-- The actual input linear section vanishes exactly on its original
homogeneous source hyperplane at the same projective image point. -/
theorem native_input_linear_section_zero_iff_source_equation
    (ν : Fin 4 → E) (z : N) (a : Fin 4) (ha : z ∈ U a) :
    (N).presheaf.germ (U a) z ha
        (extendedClosedGaussHyperplaneGlobalCoefficient H I E hH e
          (extendedClosedGaussInputLinearSection H I E hH e ν) a) ∈
            IsLocalRing.maximalIdeal ((N).presheaf.stalk z) ↔
      linearFormPolynomial ν ∈ ((f) z).asHomogeneousIdeal := by
  rw [native_input_linear_section_germ_eq_polynomial]
  exact native_polynomial_germ_mem_maximal_iff_projective_equation H I E hH e
    (linearFormPolynomial ν) (extendedClosedGaussInputLinearPolynomial_homogeneous E ν) z a ha

end DimensionFourDependence
