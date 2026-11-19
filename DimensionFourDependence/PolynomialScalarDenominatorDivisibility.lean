import DimensionFourDependence.PolynomialScalarFactorRegularity
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic

/-! # A reduced parameter denominator divides a power of the source factor

The relation A(t) Z^d=H has leading coefficient lc(A) Z^d as a
polynomial relation for t. Integral normalization makes Z^d t integral,
since lc(A) is a nonzero original-field scalar. Normality makes it an
actual source-ring value. Original coprimality of t=p/q then gives q|Z^d.
-/

namespace DimensionFourDependence

open Polynomial

set_option maxHeartbeats 2000000

variable {K R F : Type*} [Field K] [CommRing R] [IsDomain R] [Field F]
    [Algebra K R] [Algebra K F] [Algebra R F] [IsScalarTower K R F]

/-- A nonconstant polynomial scalar relation makes the source factor
power times the parameter integral over the original source ring. -/
theorem source_factor_power_parameter_isIntegral
    (t : F) (Z : R) (hZ : Z ≠ 0) (A : Polynomial K) (hA : 0 < A.natDegree)
    (d : ℕ) (H : R)
    (hH : algebraMap R F H = Polynomial.aeval t A * (algebraMap R F Z) ^ d) :
    IsIntegral R (algebraMap R F (Z ^ d) * t) := by
  classical
  have hA0 : A ≠ 0 := by intro h; simp [h] at hA
  let P : Polynomial R := C (Z ^ d) * A.map (algebraMap K R) - C H
  have hdeg : 0 < (C (Z ^ d) * A.map (algebraMap K R)).degree := by
    apply natDegree_pos_iff_degree_pos.mp
    simpa only [natDegree_C_mul (pow_ne_zero d hZ), natDegree_map] using hA
  have hLC : P.leadingCoeff = Z ^ d * algebraMap K R A.leadingCoeff := by
    dsimp only [P]
    rw [leadingCoeff_sub_of_degree_lt (degree_C_le.trans_lt hdeg),
      leadingCoeff_mul, leadingCoeff_C, leadingCoeff_map]
  have hP : Polynomial.aeval t P = 0 := by
    simp only [P, map_sub, map_mul, aeval_C, aeval_map_algebraMap, map_pow]
    rw [hH]
    ring
  have hI := isIntegral_leadingCoeff_smul P t hP
  have hunitR : algebraMap K R A.leadingCoeff⁻¹ * algebraMap K R A.leadingCoeff = 1 := by
    rw [← map_mul, inv_mul_cancel₀ (leadingCoeff_ne_zero.mpr hA0), map_one]
  have hunitF : algebraMap R F (algebraMap K R A.leadingCoeff⁻¹) *
      algebraMap R F (algebraMap K R A.leadingCoeff) = 1 := by
    rw [← map_mul, hunitR, map_one]
  apply IsIntegral.of_mul_unit hunitF
  convert hI using 1
  rw [Algebra.smul_def, hLC, map_mul]
  ring

/-- Normality constructs the actual regular value Z^d t from the
original polynomial scalar relation. -/
theorem source_factor_power_parameter_regular
    [IsIntegrallyClosed R] [IsFractionRing R F]
    (t : F) (Z : R) (hZ : Z ≠ 0) (A : Polynomial K) (hA : 0 < A.natDegree)
    (d : ℕ) (H : R)
    (hH : algebraMap R F H = Polynomial.aeval t A * (algebraMap R F Z) ^ d) :
    ∃ Y : R, algebraMap R F Y = algebraMap R F (Z ^ d) * t :=
  IsIntegrallyClosed.algebraMap_eq_of_integral
    (source_factor_power_parameter_isIntegral t Z hZ A hA d H hH)

/-- The entire original reduced source denominator divides Z^d.
This includes every source-prime divisor without choosing a valuation
or assuming a pole-order comparison. -/
theorem reduced_parameter_denominator_dvd_source_factor_power
    [IsIntegrallyClosed R] [IsFractionRing R F] [UniqueFactorizationMonoid R]
    (p q : R) (hq : q ≠ 0) (hrel : IsRelPrime p q)
    (Z : R) (hZ : Z ≠ 0) (A : Polynomial K) (hA : 0 < A.natDegree)
    (d : ℕ) (H : R)
    (hH : algebraMap R F H = Polynomial.aeval (algebraMap R F p / algebraMap R F q) A *
      (algebraMap R F Z) ^ d) : q ∣ Z ^ d := by
  have hqF : algebraMap R F q ≠ 0 := by
    simpa only [map_zero] using (IsFractionRing.injective R F).ne hq
  obtain ⟨Y, hY⟩ := source_factor_power_parameter_regular
    (algebraMap R F p / algebraMap R F q) Z hZ A hA d H hH
  have hcross : Z ^ d * p = q * Y := by
    apply IsFractionRing.injective R F
    simp only [map_mul]
    have heq := congrArg (fun y : F => y * algebraMap R F q) hY
    rw [mul_assoc, div_mul_cancel₀ _ hqF] at heq
    exact heq.symm.trans (mul_comm _ _)
  apply hrel.symm.dvd_of_dvd_mul_left
  exact ⟨Y, by rw [mul_comm p]; exact hcross⟩

end DimensionFourDependence
