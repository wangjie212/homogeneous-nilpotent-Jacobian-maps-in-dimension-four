import DimensionFourDependence.GenericReducedHomogeneousPencil

/-! # Nilpotence and the inactive square divisors force the active pencil minor -/

namespace DimensionFourDependence

open MvPolynomial Matrix

set_option maxHeartbeats 3500000

variable {K : Type*} [Field K] {n : ℕ}
local notation "P₀" => MvPolynomial (Fin n) K

/-- The original two-output, two-source Jacobian minor. -/
noncomputable def sourceJacobianMinor (f h : P₀) (j k : Fin n) : P₀ :=
  pderiv j f * pderiv k h - pderiv k f * pderiv j h

theorem sourceJacobianMinor_swap (f h : P₀) (j k : Fin n) :
    sourceJacobianMinor h f j k = -sourceJacobianMinor f h j k := by
  unfold sourceJacobianMinor
  ring

/-- The exact common-factor expansion retains the factor even when
the common factor and the pencil numerator share prime divisors. -/
theorem sourceJacobianMinor_common_factor (g a b : P₀) (j k : Fin n) :
    sourceJacobianMinor (g * a) (g * b) j k =
      g * (g * sourceJacobianMinor a b j k +
        a * (pderiv j g * pderiv k b - pderiv k g * pderiv j b) +
        b * (pderiv j a * pderiv k g - pderiv k a * pderiv j g)) := by
  simp only [sourceJacobianMinor, pderiv_mul]
  ring

theorem common_factor_divides_sourceJacobianMinor (g a b : P₀) (j k : Fin n) :
    g ∣ sourceJacobianMinor (g * a) (g * b) j k := by
  rw [sourceJacobianMinor_common_factor]
  exact dvd_mul_right _ _

/-- If one reduced output has a square pencil factor, every minor
with that output retains the full common factor times the numerator.
No coprimality between those two factors is assumed. -/
theorem common_factor_times_pencil_divides_inactive_square_minor
    (g p a b : P₀) (hsquare : p ^ 2 ∣ a) (j k : Fin n) :
    g * p ∣ sourceJacobianMinor (g * a) (g * b) j k := by
  let I : Ideal P₀ := Ideal.span {p}
  let f : P₀ →+* P₀ ⧸ I := Ideal.Quotient.mk I
  have hpa : p ∣ a := (dvd_mul_right p p).trans (by simpa only [pow_two] using hsquare)
  have hpj : p ∣ pderiv j a := polynomial_square_divisor_divides_every_partial p a
    (by simpa only [pow_two] using hsquare) j
  have hpk : p ∣ pderiv k a := polynomial_square_divisor_divides_every_partial p a
    (by simpa only [pow_two] using hsquare) k
  have hzero (r : P₀) (hr : p ∣ r) : f r = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton.mpr hr)
  let C := g * sourceJacobianMinor a b j k +
    a * (pderiv j g * pderiv k b - pderiv k g * pderiv j b) +
    b * (pderiv j a * pderiv k g - pderiv k a * pderiv j g)
  have hCzero : f C = 0 := by
    simp only [C, sourceJacobianMinor, map_add, map_mul, map_sub,
      hzero a hpa, hzero (pderiv j a) hpj, hzero (pderiv k a) hpk,
      zero_mul, mul_zero, sub_self, add_zero]
  obtain ⟨c, hc⟩ : p ∣ C := Ideal.mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp hCzero)
  refine ⟨c, ?_⟩
  rw [sourceJacobianMinor_common_factor]
  change g * C = _
  rw [hc, mul_assoc]

variable {R : Type*} [CommRing R]

/-- The full four-by-four second-trace identity as the six original
principal two-by-two minors. -/
theorem four_matrix_second_trace_principal_minor_identity
    (M : Matrix (Fin 4) (Fin 4) R) :
    Matrix.trace M ^ 2 - Matrix.trace (M ^ 2) =
      2 * ((M 0 0 * M 1 1 - M 0 1 * M 1 0) +
        (M 0 0 * M 2 2 - M 0 2 * M 2 0) +
        (M 0 0 * M 3 3 - M 0 3 * M 3 0) +
        (M 1 1 * M 2 2 - M 1 2 * M 2 1) +
        (M 1 1 * M 3 3 - M 1 3 * M 3 1) +
        (M 2 2 * M 3 3 - M 2 3 * M 3 2)) := by
  simp [pow_two, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Fin.sum_univ_succ]
  ring

variable [CharZero K]
local notation "R₀" => MvPolynomial (Fin 4) K

/-- The actual nilpotent Jacobian supplies the sum-of-principal-minors
identity, with no trace equation supplied separately. -/
theorem nilpotent_four_variable_source_principal_minors_sum_zero
    (H : Fin 4 → R₀) (hN : IsNilpotent (jac H)) :
    sourceJacobianMinor (H 0) (H 1) 0 1 + sourceJacobianMinor (H 0) (H 2) 0 2 +
      sourceJacobianMinor (H 0) (H 3) 0 3 + sourceJacobianMinor (H 1) (H 2) 1 2 +
      sourceJacobianMinor (H 1) (H 3) 1 3 + sourceJacobianMinor (H 2) (H 3) 2 3 = 0 := by
  have ht : Matrix.trace (jac H) = 0 := (Matrix.isNilpotent_trace_of_isNilpotent hN).eq_zero
  have ht2 : Matrix.trace (jac H ^ 2) = 0 :=
    (Matrix.isNilpotent_trace_of_isNilpotent (hN.pow_of_pos (by decide : (2 : ℕ) ≠ 0))).eq_zero
  have he := four_matrix_second_trace_principal_minor_identity (jac H)
  rw [ht, ht2, zero_pow (by decide : (2 : ℕ) ≠ 0), sub_self] at he
  have hs := (mul_eq_zero.mp he.symm).resolve_left (by norm_num : (2 : R₀) ≠ 0)
  simpa only [sourceJacobianMinor, jac, Matrix.of_apply] using hs

/-- The two inactive square divisors and the actual nilpotent
Jacobian force numerator divisibility of the active output-numerator
minor. The proof cancels the common factor before applying relative
primality, so no unproved common-factor coprimality is needed. -/
theorem nilpotent_inactive_square_divisors_force_active_pencil_minor_divisibility
    (H W : Fin 4 → R₀) (g p B : R₀) (hg : g ≠ 0)
    (hcommon : ∀ i, H i = g * W i) (hN : IsNilpotent (jac H))
    (hzero : g * p ^ 2 ∣ H 0) (hthree : g * p ^ 2 ∣ H 3)
    (htwo : H 2 = g * p * B) (hrel : IsRelPrime p B) :
    p ∣ sourceJacobianMinor (H 1) p 1 2 := by
  have hsquare (i : Fin 4) (hi : g * p ^ 2 ∣ H i) : p ^ 2 ∣ W i := by
    obtain ⟨b, hb⟩ := hi
    refine ⟨b, ?_⟩
    apply mul_left_cancel₀ hg
    rw [← hcommon, hb, mul_assoc]
  have hsq0 := hsquare 0 hzero
  have hsq3 := hsquare 3 hthree
  have hinactive (i j : Fin 4) (hs : p ^ 2 ∣ W i) (a b : Fin 4) :
      g * p ∣ sourceJacobianMinor (H i) (H j) a b := by
    simpa only [hcommon] using
      common_factor_times_pencil_divides_inactive_square_minor g p (W i) (W j) hs a b
  have h01 := hinactive 0 1 hsq0 0 1
  have h02 := hinactive 0 2 hsq0 0 2
  have h03 := hinactive 0 3 hsq0 0 3
  have h13 : g * p ∣ sourceJacobianMinor (H 1) (H 3) 1 3 := by
    have h := hinactive 3 1 hsq3 1 3
    rw [sourceJacobianMinor_swap] at h
    exact dvd_neg.mp h
  have h23 : g * p ∣ sourceJacobianMinor (H 2) (H 3) 2 3 := by
    have h := hinactive 3 2 hsq3 2 3
    rw [sourceJacobianMinor_swap] at h
    exact dvd_neg.mp h
  have hsum := nilpotent_four_variable_source_principal_minors_sum_zero H hN
  have hactive : g * p ∣ sourceJacobianMinor (H 1) (H 2) 1 2 := by
    have hother := dvd_add (dvd_add (dvd_add (dvd_add h01 h02) h03) h13) h23
    have heq : sourceJacobianMinor (H 1) (H 2) 1 2 =
        -(sourceJacobianMinor (H 0) (H 1) 0 1 + sourceJacobianMinor (H 0) (H 2) 0 2 +
          sourceJacobianMinor (H 0) (H 3) 0 3 + sourceJacobianMinor (H 1) (H 3) 1 3 +
          sourceJacobianMinor (H 2) (H 3) 2 3) := by linear_combination hsum
    rw [heq]
    exact dvd_neg.mpr hother
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
    have hd := dvd_sub hsumdiv (dvd_mul_right p C)
    simpa only [add_sub_cancel_right] using hd
  exact hrel.dvd_of_dvd_mul_left hdiv

end DimensionFourDependence
