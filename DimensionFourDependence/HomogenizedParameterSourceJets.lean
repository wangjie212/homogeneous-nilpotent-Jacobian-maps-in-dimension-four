import DimensionFourDependence.HomogenizedParameterPencil

/-! # Parameter orders and first source derivatives in a normalized pencil chart -/

namespace DimensionFourDependence

open MvPolynomial

set_option maxHeartbeats 3000000

variable {K : Type*} [Field K] {n : ℕ}
local notation "R₀" => MvPolynomial (Fin n) K

/-- A power of the parameter constructs the exact corresponding
source-pencil power and its polynomial homogeneous quotient. -/
theorem parameter_X_power_constructs_homogeneous_source_factorization
    (v : Polynomial K) {N s : ℕ} (hN : v.natDegree ≤ N)
    (hs : Polynomial.X ^ s ∣ v) (p q : R₀) :
    ∃ w : Polynomial K, v = Polynomial.X ^ s * w ∧ w.natDegree ≤ N - s ∧
      homogeneousParameterPolynomialValue v N p q =
        p ^ s * homogeneousParameterPolynomialValue w (N - s) p q := by
  by_cases hv : v = 0
  · refine ⟨0, by simp [hv], Nat.zero_le _, ?_⟩
    simp [hv, homogeneousParameterPolynomialValue]
  obtain ⟨w, hw⟩ := hs
  have hw0 : w ≠ 0 := by intro hz; apply hv; rw [hw, hz, mul_zero]
  have hX0 : (Polynomial.X ^ s : Polynomial K) ≠ 0 := pow_ne_zero s Polynomial.X_ne_zero
  have hdegree : s + w.natDegree = v.natDegree := by
    rw [hw, Polynomial.natDegree_mul hX0 hw0, Polynomial.natDegree_X_pow]
  have hsN : s ≤ N := by omega
  have hwN : w.natDegree ≤ N - s := by omega
  have hpoly : v.homogenize N = X (0 : Fin 2) ^ s * w.homogenize (N - s) := by
    calc
      _ = (Polynomial.X ^ s * w).homogenize (s + (N - s)) := by rw [← hw, Nat.add_sub_of_le hsN]
      _ = _ := by
        rw [Polynomial.homogenize_mul _ _ (by simp) hwN,
          Polynomial.homogenize_X_pow (le_refl s)]
        simp
  refine ⟨w, hw, hwN, ?_⟩
  rw [homogeneousParameterPolynomialValue, hpoly, map_mul, map_pow, aeval_X]
  rfl

/-- Parameter multiplicity gives divisibility in the original source
polynomial ring, even when the original parameter polynomial is zero. -/
theorem parameter_X_power_divides_original_homogeneous_source_value
    (v : Polynomial K) {N s : ℕ} (hN : v.natDegree ≤ N)
    (hs : Polynomial.X ^ s ∣ v) (p q : R₀) :
    p ^ s ∣ homogeneousParameterPolynomialValue v N p q := by
  obtain ⟨w, _hw, _hwN, hvalue⟩ :=
    parameter_X_power_constructs_homogeneous_source_factorization v hN hs p q
  exact ⟨homogeneousParameterPolynomialValue w (N - s) p q, hvalue⟩

/-- At a normalized nonbase source point, every homogeneous parameter
value is its literal constant coefficient. -/
theorem homogeneous_parameter_value_at_normalized_source_point
    (v : Polynomial K) {N : ℕ} (hN : v.natDegree ≤ N)
    (p q : R₀) (z : Fin n → K) (hp : aeval z p = 0) (hq : aeval z q = 1) :
    aeval z (homogeneousParameterPolynomialValue v N p q) = v.coeff 0 := by
  rw [homogeneousParameterPolynomialValue_algHom, hp, hq]
  simpa only [map_zero, zero_mul, one_pow, one_mul, Algebra.algebraMap_self,
    RingHom.id_apply, ← Polynomial.coeff_zero_eq_eval_zero] using
    homogeneousParameterPolynomialValue_proportional (A := K) v hN 0 1

/-- With zero constant parameter coefficient, the first derivative
of the original homogeneous value is the source pencil derivative
times the actual linear parameter coefficient. -/
theorem homogeneous_parameter_value_first_source_derivative_at_normalized_point
    (v : Polynomial K) {N : ℕ} (hN : v.natDegree ≤ N) (hv0 : v.coeff 0 = 0)
    (p q : R₀) (z : Fin n → K) (hp : aeval z p = 0) (hq : aeval z q = 1) (j : Fin n) :
    aeval z (pderiv j (homogeneousParameterPolynomialValue v N p q)) =
      aeval z (pderiv j p) * v.coeff 1 := by
  have hX : Polynomial.X ^ 1 ∣ v := by
    simpa only [pow_one] using (Polynomial.X_dvd_iff.mpr hv0)
  obtain ⟨w, hw, hwN, hvalue⟩ :=
    parameter_X_power_constructs_homogeneous_source_factorization v hN hX p q
  have hc1 : v.coeff 1 = w.coeff 0 := by
    rw [hw, pow_one]
    simp
  have hquot := homogeneous_parameter_value_at_normalized_source_point w hwN p q z hp hq
  rw [hvalue, pow_one, pderiv_mul, map_add, map_mul, map_mul, hp, zero_mul, add_zero, hquot, hc1]

/-- Vanishing of the first two parameter coefficients forces the
actual original source value to be divisible by the square pencil
member. No rational expression or generic-point restriction is used. -/
theorem zero_parameter_first_jet_forces_original_source_square_divisibility
    (v : Polynomial K) {N : ℕ} (hN : v.natDegree ≤ N)
    (hv0 : v.coeff 0 = 0) (hv1 : v.coeff 1 = 0) (p q : R₀) :
    p ^ 2 ∣ homogeneousParameterPolynomialValue v N p q := by
  apply parameter_X_power_divides_original_homogeneous_source_value v hN
  apply Polynomial.X_pow_dvd_iff.mpr
  intro k hk
  interval_cases k <;> assumption

end DimensionFourDependence
