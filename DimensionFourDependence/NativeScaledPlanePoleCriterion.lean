import DimensionFourDependence.NativePolynomialGermHom
import DimensionFourDependence.RegularQuotientIdealPowers
import DimensionFourDependence.ScaledPlaneLocalHeightOneBranches
import DimensionFourDependence.NativePencilCommonFactorContradiction

/-! # The actual scaled-plane quotient has a pole over every source divisor in L

If its quotient were regular, its numerator and scaled-power output
coordinate would both have local multiplicity at least d. The original
ruling-span relations then give this order for all four original
components. The proved source common-factor bound contradicts primitivity.
-/

namespace DimensionFourDependence

open MvPolynomial AlgebraicGeometry

attribute [local instance] MvPolynomial.gradedAlgebra

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
local notation "V" a:max => extendedClosedGaussNormalizationChartOpen H I E hH e (finSuccEquiv' a)
local notation "m" => extendedClosedGaussNormalizationSourceMorphism H I E hH e
local notation "w" => extendedClosedGaussNormalizationHyperplaneWeight H I E hH e
local notation "ι" => extendedClosedGaussSourceCoefficientHom H I E
local notation "O" => extendedClosedGaussOutputLinearPolynomial H I E
local notation "germ" P:max z:max a:max ha:max => extendedClosedGaussPolynomialCoefficientGerm H I E hH e P z a ha

local instance nativeScaledPlanePoleCriterionIntegral : IsIntegral N :=
  extendedClosedGaussNormalizationScheme_isIntegral H I E hH e
noncomputable local instance nativeScaledPlanePoleCriterionAlgebra : Algebra E (N).functionField :=
  extendedClosedGaussOwnFunctionFieldAlgebra H I E hH e

/-- At an actual normalization point over an original source
divisor, the scaled normal-plane identity and ruling-span coordinates
force the exact quotient to be nonregular whenever the normal vanishes.
All original component multiplicities are derived from regularity. -/
theorem no_native_scaled_plane_quotient_regular_over_source_divisor
    (s n : Fin 4 → E) (L : MvPolynomial (Fin 4) E) (hL : L.IsHomogeneous 1)
    (hL0 : aeval (w) L ≠ 0) (c : E)
    (hpower : aeval (w) ((O) s) = algebraMap E (N).functionField c * (aeval (w) L) ^ d)
    (bS bN : Fin 4 → E)
    (hspan : ∀ i, aeval (w) (MvPolynomial.map (ι) (H i)) =
      algebraMap E (N).functionField (bS i) * aeval (w) ((O) s) +
        algebraMap E (N).functionField (bN i) * aeval (w) ((O) n))
    (z : N) (hcodim : Order.coheight ((m) z) = 1) (a : Fin 4) (ha : z ∈ V a)
    (hlmax : germ L z a ha ∈ IsLocalRing.maximalIdeal ((N).presheaf.stalk z))
    (P : Fin 4 → MvPolynomial (Fin 4) K) (g : MvPolynomial (Fin 4) K) {c₀ fdeg : ℕ}
    (hg : g ≠ 0) (hgh : g.IsHomogeneous c₀) (hP : IsHomogMap P fdeg)
    (hprim : IsPrimitiveVec P) (hHP : H = fun i => g * P i) (hdeg : g.totalDegree < d) :
    ¬ IsLocalization.IsInteger ((N).presheaf.stalk z)
      (aeval (w) ((O) n) / (aeval (w) L) ^ d) := by
  intro hreg
  let R := (N).presheaf.stalk z
  let J := IsLocalRing.maximalIdeal R
  have hSh := extendedClosedGaussOutputLinearPolynomial_homogeneous H I E hH s
  have hNh := extendedClosedGaussOutputLinearPolynomial_homogeneous H I E hH n
  have hl0 : germ L z a ha ≠ 0 := by
    intro he
    exact hL0 ((extendedClosedGaussPolynomialCoefficientGerm_eq_zero_iff H I E hH e L hL z a ha).mp he)
  have hreg' : IsLocalization.IsInteger R
      (algebraMap R (N).functionField (germ ((O) n) z a ha) /
        (algebraMap R (N).functionField (germ L z a ha)) ^ d) := by
    convert hreg using 1
    rw [extendedClosedGaussPolynomialCoefficientGerm_value H I E hH e _ hNh,
      extendedClosedGaussPolynomialCoefficientGerm_value H I E hH e _ hL]
    simpa only [pow_one] using homogeneous_frame_quotient_cancel
      (aeval (w) ((O) n)) (aeval (w) L) ((w) a)
      (extendedClosedGaussNormalizationHyperplaneWeight_ne_zero H I E hH e a) d
  have hnJ : germ ((O) n) z a ha ∈ J ^ d :=
    regular_quotient_numerator_mem_ideal_power J _ _ hl0 hlmax d hreg'
  have hsJ : germ ((O) s) z a ha ∈ J ^ d := by
    rw [native_scaled_power_identity_germs H I E hH e _ L hSh hL c hpower]
    exact (J ^ d).mul_mem_left _ (Ideal.pow_mem_pow hlmax d)
  have horders (i : Fin 4) : germ (MvPolynomial.map (ι) (H i)) z a ha ∈ J ^ d := by
    rw [extendedClosedGaussPolynomialCoefficientGerm_linear_combination H I E hH e
      _ ((O) s) ((O) n) ((hH i).map _) hSh hNh (bS i) (bN i) (hspan i)]
    exact (J ^ d).add_mem ((J ^ d).mul_mem_left _ hsJ) ((J ^ d).mul_mem_left _ hnJ)
  obtain ⟨Δ, hΔ, hΔhom, hdiv, hdegree, hsmall⟩ :=
    actual_native_component_orders_common_factor_degree H I E hH e z hcodim a ha
      P g hg hgh hP hprim hHP d horders
  exact (not_le_of_gt hdeg) hsmall

end DimensionFourDependence
