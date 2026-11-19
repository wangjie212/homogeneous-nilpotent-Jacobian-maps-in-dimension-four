import DimensionFourDependence.ZeroPoleLevelClosure
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.Algebra.Polynomial.Reverse

/-! # A polynomial relation with a unit value makes the level reciprocal integral -/

namespace DimensionFourDependence

open Polynomial

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000

variable {R F : Type*} [CommRing R] [Nontrivial R] [Field F] [Algebra R F]

/-- Reversing the Taylor translate of an actual polynomial relation
proves integrality of a level reciprocal whenever the polynomial's
value at that level is a unit of the original coefficient ring. -/
theorem polynomial_relation_unit_value_integral_level_reciprocal
    (P : Polynomial R) (f : F) (c : R)
    (hroot : aeval f P = 0) (hunit : IsUnit (P.eval c)) :
    IsIntegral R ((f - algebraMap R F c)⁻¹) := by
  have hx : f - algebraMap R F c ≠ 0 := by
    intro he
    have hf : f = algebraMap R F c := sub_eq_zero.mp he
    have hz : algebraMap R F (P.eval c) = 0 := by
      rw [hf] at hroot
      exact (eval₂_at_apply (algebraMap R F) c).symm.trans hroot
    have hu := hunit.map (algebraMap R F)
    rw [hz] at hu
    exact not_isUnit_zero hu
  let Q := taylor c P
  have hQroot : aeval (f - algebraMap R F c) Q = 0 := by
    change (P.comp (X + C c)).eval₂ (algebraMap R F) (f - algebraMap R F c) = 0
    rw [eval₂_comp, eval₂_add, eval₂_X, eval₂_C, sub_add_cancel]
    exact hroot
  letI : Invertible (f - algebraMap R F c) := invertibleOfNonzero hx
  have hrev : aeval ((f - algebraMap R F c)⁻¹) Q.reverse = 0 := by
    simpa only [aeval_def, invOf_eq_inv] using
      (eval₂_reverse_eq_zero_iff (algebraMap R F) (f - algebraMap R F c) Q).mpr hQroot
  have hcoeff : Q.coeff 0 ≠ 0 := by
    simpa only [Q, taylor_coeff_zero] using hunit.ne_zero
  have hlead : Q.reverse.leadingCoeff = P.eval c := by
    rw [reverse_leadingCoeff, trailingCoeff_eq_coeff_zero hcoeff]
    exact taylor_coeff_zero c P
  obtain ⟨u, hu⟩ := hlead ▸ hunit
  have hint := isIntegral_leadingCoeff_smul Q.reverse ((f - algebraMap R F c)⁻¹) hrev
  apply IsIntegral.of_mul_unit (y := algebraMap R F Q.reverse.leadingCoeff) (r := (↑u⁻¹ : R))
  · rw [← hu, ← map_mul]
    simp only [Units.inv_mul, map_one]
  · simpa only [Algebra.smul_def, mul_comm] using hint

variable [IsDomain R] [IsFractionRing R F] [IsIntegrallyClosed R]

/-- Normality turns the constructed integral reciprocal into an
actual regular element of the original local fraction field. -/
theorem normal_polynomial_relation_unit_value_regular_level_reciprocal
    (P : Polynomial R) (f : F) (c : R)
    (hroot : aeval f P = 0) (hunit : IsUnit (P.eval c)) :
    IsLocalization.IsInteger R ((f - algebraMap R F c)⁻¹) :=
  (isIntegrallyClosed_iff F).mp inferInstance
    (polynomial_relation_unit_value_integral_level_reciprocal P f c hroot hunit)

end DimensionFourDependence
