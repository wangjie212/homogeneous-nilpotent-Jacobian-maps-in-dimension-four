import DimensionFourDependence.HomogenizedParameterSourceJets
import DimensionFourDependence.NilpotentPencilMinorDivisibility

/-! # The original normalized active output constructs the coprime quotient and trace minor -/

namespace DimensionFourDependence

open MvPolynomial Matrix

set_option maxHeartbeats 3000000

variable {K : Type*} [Field K] {n : ℕ}
local notation "P₀" => MvPolynomial (Fin n) K

/-- A simple zero of the actual parameter polynomial gives a source
numerator factor with relatively prime quotient. Its exact remainder
modulo that numerator comes from the nonzero linear parameter coefficient. -/
theorem simple_parameter_zero_constructs_relPrime_source_numerator_quotient
    (v : Polynomial K) {N : ℕ} (hN : v.natDegree ≤ N)
    (hv0 : v.coeff 0 = 0) (hv1 : v.coeff 1 ≠ 0)
    (p q : P₀) (hrel : IsRelPrime p q) :
    ∃ B : P₀, homogeneousParameterPolynomialValue v N p q = p * B ∧ IsRelPrime p B := by
  have hX : Polynomial.X ^ 1 ∣ v := by simpa only [pow_one] using Polynomial.X_dvd_iff.mpr hv0
  obtain ⟨w, hw, hwN, hW⟩ := parameter_X_power_constructs_homogeneous_source_factorization v hN hX p q
  have hc : w.coeff 0 ≠ 0 := by
    have he : v.coeff 1 = w.coeff 0 := by rw [hw, pow_one]; simp
    exact he ▸ hv1
  let B := homogeneousParameterPolynomialValue w (N - 1) p q
  have hrem : p ∣ B - q ^ (N - 1) * C (w.coeff 0) := by
    simpa only [map_zero, zero_mul, sub_zero, ← Polynomial.coeff_zero_eq_eval_zero] using
      source_pencil_divides_homogeneous_parameter_remainder w hwN p q 0
  have hunit : IsUnit (C (w.coeff 0) : P₀) := (isUnit_iff_ne_zero.mpr hc).map C
  have hcop : IsRelPrime p (q ^ (N - 1) * C (w.coeff 0)) :=
    hrel.pow_right.mul_right hunit.isRelPrime_right
  have hB : IsRelPrime p B := by
    intro δ hδp hδB
    apply hcop hδp
    have he : q ^ (N - 1) * C (w.coeff 0) = B - (B - q ^ (N - 1) * C (w.coeff 0)) := by ring
    rw [he]
    exact dvd_sub hδB (hδp.trans hrem)
  exact ⟨B, by simpa only [pow_one] using hW, hB⟩

variable [CharZero K]
local notation "R₀" => MvPolynomial (Fin 4) K

/-- The actual normalized primitive polynomial pencil and the
nilpotent original Jacobian construct the active numerator-minor
divisibility. The simple active parameter zero and its coprime source
quotient are derived, rather than supplied. -/
theorem normalized_nilpotent_source_pencil_forces_active_minor_divisibility
    (H : Fin 4 → R₀) (p q g : R₀) (hg : g ≠ 0) (hrel : IsRelPrime p q)
    (z : Fin 4 → K) (hpz : aeval z p = 0) (hqz : aeval z q = 1)
    (v : Fin 4 → Polynomial K) {N : ℕ} (hN : ∀ i, (v i).natDegree ≤ N)
    (hfactor : ∀ i, H i = g * homogeneousParameterPolynomialValue (v i) N p q)
    (hv20 : (v 2).coeff 0 = 0) (hder2 : aeval z (pderiv 1 (H 2)) = 1)
    (hzero : g * p ^ 2 ∣ H 0) (hthree : g * p ^ 2 ∣ H 3)
    (hnil : IsNilpotent (jac H)) : p ∣ sourceJacobianMinor (H 1) p 1 2 := by
  have hW0 := homogeneous_parameter_value_at_normalized_source_point (v 2) (hN 2) p q z hpz hqz
  have hfirst := homogeneous_parameter_value_first_source_derivative_at_normalized_point
    (v 2) (hN 2) hv20 p q z hpz hqz 1
  have he : aeval z g * aeval z (pderiv 1 p) * (v 2).coeff 1 = 1 := by
    have h := congrArg (fun f => aeval z (pderiv 1 f)) (hfactor 2)
    rw [hder2, pderiv_mul] at h
    simp only [map_add, map_mul] at h
    rw [hW0, hv20, mul_zero, zero_add, hfirst] at h
    simpa only [mul_assoc] using h.symm
  have hv21 : (v 2).coeff 1 ≠ 0 := by
    intro hz
    rw [hz, mul_zero] at he
    exact zero_ne_one he
  obtain ⟨B, hB, hcop⟩ := simple_parameter_zero_constructs_relPrime_source_numerator_quotient
    (v 2) (hN 2) hv20 hv21 p q hrel
  have htwo : H 2 = g * p * B := by rw [hfactor 2, hB, mul_assoc]
  exact nilpotent_inactive_square_divisors_force_active_pencil_minor_divisibility H
    (fun i => homogeneousParameterPolynomialValue (v i) N p q) g p B hg hfactor hnil hzero hthree htwo hcop

end DimensionFourDependence
