import DimensionFourDependence.ActualChosenRootAlternatives
import DimensionFourDependence.ProportionalRootFieldIdentities

/-! # Exact native root identities in the two remaining proportional cases

Proportionality on the actual ruling gives an equality of the actual
native output values. The original rational root formula then supplies
the precise scalar plane root or the degree-(d-1) denominator factor.
-/

namespace DimensionFourDependence

open MvPolynomial Matrix AlgebraicGeometry

universe u

set_option quotPrecheck false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

variable {K : Type u} [Field K] [CharZero K]
    (H : Fin 4 → MvPolynomial (Fin 4) K) (I : ImageRelationWitness H)
    (E : Type u) [Field E] [Algebra (closedGaussParameterField H I) E]
    [Algebra.IsAlgebraic (closedGaussParameterField H I) E]
    {d : ℕ} (hH : IsHomogMap H d) (e : RatFunc K ≃ₐ[K] closedGaussParameterField H I)
    (hd : 0 < d) (hind : ¬ ComponentsDependent H) (hGauss : gaussImageDimension H I = 1)

local notation "N" => extendedClosedGaussNormalizationScheme H I E hH e
local notation "w" => extendedClosedGaussNormalizationHyperplaneWeight H I E hH e
local notation "ν₀" => extendedClosedGaussChosenRulingMatrix H I E hH hd hind hGauss 0
local notation "W₀" => LinearMap.ker (extendedClosedGaussChosenRulingMatrix H I E hH hd hind hGauss).toLin'
local notation "O" => extendedClosedGaussOutputLinearPolynomial H I E
local notation "R" => rulingFormRestriction (W₀)
local notation "Lₜ" => ∑ i, algebraMap E (N).functionField ((ν₀) i) * (w) i

local instance nativeProportionalRootIdentitiesIntegral : IsIntegral N :=
  extendedClosedGaussNormalizationScheme_isIntegral H I E hH e
noncomputable local instance nativeProportionalRootIdentitiesAlgebra : Algebra E (N).functionField :=
  extendedClosedGaussOwnFunctionFieldAlgebra H I E hH e

/-- Proportional forms on the actual chosen ruling retain precisely
their proportional native output values. -/
theorem extendedClosedGauss_proportional_ruling_output_value
    (cS cN : Fin 4 → E) (β : E) (hβ : (R) cS = β • (R) cN) :
    aeval (w) ((O) cS) = algebraMap E (N).functionField β * aeval (w) ((O) cN) := by
  have hlinear : (R) cS = β • (R) cN + (0 : E) • (R) 0 := by
    simpa only [zero_smul, add_zero] using hβ
  simpa only [map_zero, zero_mul, add_zero] using
    extendedClosedGauss_chosen_ruling_binary_output_relation H I E hH e hd hind hGauss cS cN 0 β 0 hlinear

/-- In the proportional m,n case, the actual constructed root is
the exact inverse-parameter scalar multiple of the chosen tangent plane. -/
theorem native_root_of_proportional_denominator_is_scaled_plane
    (cM cN : Fin 4 → E) (r : (N).functionField) (hr : r ≠ 0)
    (γ : E) (hγ : γ ≠ 0) (hMN : (R) cM = γ • (R) cN)
    (hformula : r = aeval (w) ((O) cN) * (Lₜ) / aeval (w) ((O) cM)) :
    r = algebraMap E (N).functionField γ⁻¹ * (Lₜ) := by
  have hNvalue : aeval (w) ((O) cN) ≠ 0 := by
    intro hz
    apply hr
    rw [hformula, hz, zero_mul, zero_div]
  simpa only [map_inv₀] using rational_root_of_proportional_denominator
    r (aeval (w) ((O) cM)) (aeval (w) ((O) cN)) (Lₜ) (algebraMap E (N).functionField γ)
    ((map_ne_zero (algebraMap E (N).functionField)).mpr hγ) hNvalue
    (extendedClosedGauss_proportional_ruling_output_value H I E hH e hd hind hGauss cM cN γ hMN) hformula

/-- The first remaining case gives the paper's actual native
output-linear form as a nonzero parameter multiple of L_t^d. -/
theorem native_proportional_denominator_source_power
    (cS cM cN : Fin 4 → E) (r : (N).functionField) (hr : r ≠ 0)
    (hroot : r ^ d = aeval (w) ((O) cS))
    (γ : E) (hγ : γ ≠ 0) (hMN : (R) cM = γ • (R) cN)
    (hformula : r = aeval (w) ((O) cN) * (Lₜ) / aeval (w) ((O) cM)) :
    aeval (w) ((O) cS) = (algebraMap E (N).functionField γ⁻¹) ^ d * (Lₜ) ^ d := by
  rw [← hroot, native_root_of_proportional_denominator_is_scaled_plane H I E hH e hd hind hGauss
    cM cN r hr γ hγ hMN hformula, mul_pow]

/-- In the proportional s,n case, the actual native numerator
and denominator values have the exact factors preceding (4.6). -/
theorem native_root_proportional_power_output_values
    (cS cM cN : Fin 4 → E) (r : (N).functionField) (hr : r ≠ 0)
    (hroot : r ^ d = aeval (w) ((O) cS)) (hm : aeval (w) ((O) cM) ≠ 0)
    (β : E) (hβ : β ≠ 0) (hSN : (R) cS = β • (R) cN)
    (hformula : r = aeval (w) ((O) cN) * (Lₜ) / aeval (w) ((O) cM)) :
    aeval (w) ((O) cN) = algebraMap E (N).functionField β⁻¹ * r ^ d ∧
      aeval (w) ((O) cM) = algebraMap E (N).functionField β⁻¹ * r ^ (d - 1) * (Lₜ) := by
  simpa only [map_inv₀] using rational_root_of_proportional_power_values
    r (aeval (w) ((O) cM)) (aeval (w) ((O) cN)) (aeval (w) ((O) cS)) (Lₜ)
    (algebraMap E (N).functionField β) hd hr ((map_ne_zero (algebraMap E (N).functionField)).mpr hβ) hm hroot
    (extendedClosedGauss_proportional_ruling_output_value H I E hH e hd hind hGauss cS cN β hSN) hformula

end DimensionFourDependence
