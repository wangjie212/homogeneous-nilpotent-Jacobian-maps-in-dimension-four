import DimensionFourDependence.NormalizedPencilActiveMinor
import DimensionFourDependence.TernaryNormalizedParameterJets

/-! # The three-dimensional nilpotent traces force the actual active pencil minor -/

namespace DimensionFourDependence

open MvPolynomial Matrix

set_option maxHeartbeats 3500000

variable {R : Type*} [CommRing R]

/-- The exact three-by-three second-trace identity in the three
original principal two-by-two minors. -/
theorem three_matrix_second_trace_principal_minor_identity (M : Matrix (Fin 3) (Fin 3) R) :
    Matrix.trace M ^ 2 - Matrix.trace (M ^ 2) =
      2 * ((M 0 0 * M 1 1 - M 0 1 * M 1 0) +
        (M 0 0 * M 2 2 - M 0 2 * M 2 0) +
        (M 1 1 * M 2 2 - M 1 2 * M 2 1)) := by
  simp [pow_two, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Fin.sum_univ_succ]
  ring

variable {K : Type*} [Field K] [CharZero K]
local notation "R₀" => MvPolynomial (Fin 3) K

theorem nilpotent_ternary_source_principal_minors_sum_zero
    (H : Fin 3 → R₀) (hN : IsNilpotent (jac H)) :
    sourceJacobianMinor (H 0) (H 1) 0 1 + sourceJacobianMinor (H 0) (H 2) 0 2 +
      sourceJacobianMinor (H 1) (H 2) 1 2 = 0 := by
  have ht : Matrix.trace (jac H) = 0 := (Matrix.isNilpotent_trace_of_isNilpotent hN).eq_zero
  have ht2 : Matrix.trace (jac H ^ 2) = 0 :=
    (Matrix.isNilpotent_trace_of_isNilpotent (hN.pow_of_pos (by decide : (2 : ℕ) ≠ 0))).eq_zero
  have he := three_matrix_second_trace_principal_minor_identity (jac H)
  rw [ht, ht2, zero_pow (by decide : (2 : ℕ) ≠ 0), sub_self] at he
  have hs := (mul_eq_zero.mp he.symm).resolve_left (by norm_num : (2 : R₀) ≠ 0)
  simpa only [sourceJacobianMinor, jac, Matrix.of_apply] using hs

/-- The inactive square divisor and the actual nilpotent Jacobian
force the active numerator minor, retaining and then cancelling the
common scalar before using the coprime active quotient. -/
theorem ternary_nilpotent_inactive_square_divisor_forces_active_pencil_minor
    (H W : Fin 3 → R₀) (g p B : R₀) (hg : g ≠ 0)
    (hcommon : ∀ i, H i = g * W i) (hN : IsNilpotent (jac H))
    (hzero : g * p ^ 2 ∣ H 0) (htwo : H 2 = g * p * B) (hrel : IsRelPrime p B) :
    p ∣ sourceJacobianMinor (H 1) p 1 2 := by
  have hsq0 : p ^ 2 ∣ W 0 := by
    obtain ⟨b, hb⟩ := hzero
    refine ⟨b, ?_⟩
    apply mul_left_cancel₀ hg
    rw [← hcommon, hb, mul_assoc]
  have hinactive (j a b : Fin 3) : g * p ∣ sourceJacobianMinor (H 0) (H j) a b := by
    simpa only [hcommon] using
      common_factor_times_pencil_divides_inactive_square_minor g p (W 0) (W j) hsq0 a b
  have hsum := nilpotent_ternary_source_principal_minors_sum_zero H hN
  have hactive : g * p ∣ sourceJacobianMinor (H 1) (H 2) 1 2 := by
    have heq : sourceJacobianMinor (H 1) (H 2) 1 2 =
        -(sourceJacobianMinor (H 0) (H 1) 0 1 + sourceJacobianMinor (H 0) (H 2) 0 2) := by
      linear_combination hsum
    rw [heq]
    exact dvd_neg.mpr (dvd_add (hinactive 1 0 1) (hinactive 2 0 2))
  obtain ⟨C, hC⟩ : g ∣ sourceJacobianMinor (H 1) (g * B) 1 2 := by
    rw [hcommon 1]
    exact common_factor_divides_sourceJacobianMinor g (W 1) B 1 2
  have hprod : sourceJacobianMinor (H 1) (H 2) 1 2 =
      g * (B * sourceJacobianMinor (H 1) p 1 2 + p * C) := by
    rw [htwo]
    have he : sourceJacobianMinor (H 1) (g * p * B) 1 2 =
        g * B * sourceJacobianMinor (H 1) p 1 2 +
          p * sourceJacobianMinor (H 1) (g * B) 1 2 := by
      simp only [sourceJacobianMinor, pderiv_mul]
      ring
    rw [he, hC]
    ring
  obtain ⟨A, hA⟩ := hactive
  have hcancel : B * sourceJacobianMinor (H 1) p 1 2 + p * C = p * A := by
    apply mul_left_cancel₀ hg
    rw [← hprod, hA, mul_assoc]
  have hdiv : p ∣ B * sourceJacobianMinor (H 1) p 1 2 := by
    have hsumdiv : p ∣ B * sourceJacobianMinor (H 1) p 1 2 + p * C := ⟨A, hcancel⟩
    simpa only [add_sub_cancel_right] using dvd_sub hsumdiv (dvd_mul_right p C)
  exact hrel.dvd_of_dvd_mul_left hdiv

/-- The original normalized active jet constructs the simple
parameter coefficient and coprime quotient needed by the actual
three-variable trace argument. -/
theorem ternary_normalized_nilpotent_source_pencil_forces_active_minor_divisibility
    (H : Fin 3 → R₀) (p q g : R₀) (hg : g ≠ 0) (hrel : IsRelPrime p q)
    (z : Fin 3 → K) (hpz : aeval z p = 0) (hqz : aeval z q = 1)
    (v : Fin 3 → Polynomial K) {N : ℕ} (hN : ∀ i, (v i).natDegree ≤ N)
    (hfactor : ∀ i, H i = g * homogeneousParameterPolynomialValue (v i) N p q)
    (hv20 : (v 2).coeff 0 = 0) (hder2 : aeval z (pderiv 1 (H 2)) = 1)
    (hzero : g * p ^ 2 ∣ H 0) (hnil : IsNilpotent (jac H)) :
    p ∣ sourceJacobianMinor (H 1) p 1 2 := by
  have hW0 := homogeneous_parameter_value_at_normalized_source_point (v 2) (hN 2) p q z hpz hqz
  have hfirst := homogeneous_parameter_value_first_source_derivative_at_normalized_point
    (v 2) (hN 2) hv20 p q z hpz hqz 1
  have he : aeval z g * aeval z (pderiv 1 p) * (v 2).coeff 1 = 1 := by
    have h := congrArg (fun f => aeval z (pderiv 1 f)) (hfactor 2)
    rw [hder2, pderiv_mul] at h
    simp only [map_add, map_mul] at h
    rw [hW0, hv20, mul_zero, zero_add, hfirst] at h
    simpa only [mul_assoc] using h.symm
  have hv21 : (v 2).coeff 1 ≠ 0 := by intro hz; rw [hz, mul_zero] at he; exact zero_ne_one he
  obtain ⟨B, hB, hcop⟩ := simple_parameter_zero_constructs_relPrime_source_numerator_quotient
    (v 2) (hN 2) hv20 hv21 p q hrel
  have htwo : H 2 = g * p * B := by rw [hfactor 2, hB, mul_assoc]
  exact ternary_nilpotent_inactive_square_divisor_forces_active_pencil_minor H
    (fun i => homogeneousParameterPolynomialValue (v i) N p q) g p B hg hfactor hnil hzero htwo hcop

end DimensionFourDependence
