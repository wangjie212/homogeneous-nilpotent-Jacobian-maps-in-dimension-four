import DimensionFourDependence.TwoAxisKernelTraceReduction

/-! # The Wronskian kernel and original Euler equations force a radial binary output -/

namespace DimensionFourDependence

variable {F : Type*} [Field F]

set_option maxHeartbeats 2000000

/-- The kernel of a nonzero binary covector containing a vector with
nonzero first coordinate has the exact original cross equation. -/
theorem binary_covector_common_kernel_cross_equation
    (b x v : Fin 2 → F) (hb : b ≠ 0) (hx : x 0 ≠ 0)
    (hbx : b 0 * x 0 + b 1 * x 1 = 0)
    (hbv : b 0 * v 0 + b 1 * v 1 = 0) : x 0 * v 1 = x 1 * v 0 := by
  have hb1 : b 1 ≠ 0 := by
    intro hz
    have hb0 : b 0 = 0 := (mul_eq_zero.mp (by simpa only [hz, zero_mul, add_zero] using hbx)).resolve_right hx
    apply hb
    funext i
    fin_cases i <;> assumption
  apply mul_left_cancel₀ hb1
  linear_combination x 0 * hbv - v 0 * hbx

/-- The two trace constraints and Euler identities, evaluated in the
original source, force the first two outputs to be radial when their
vertical derivative is nonzero. No integration or invariant-coordinate
factorization is assumed. -/
theorem binary_trace_constraints_and_euler_force_radial_outputs
    (M : Matrix (Fin 4) (Fin 4) F) (b x U : Fin 2 → F) (v : Fin 4 → F)
    (q p z w d : F) (hb : b ≠ 0) (hx : x 0 ≠ 0) (hd : d ≠ 0)
    (hv : (fun i : Fin 2 => v (i.castAdd 2)) ≠ 0)
    (hcol2 : ∀ i, M i 2 = q * v i) (hcol3 : ∀ i, M i 3 = -p * v i)
    (hbx : b 0 * x 0 + b 1 * x 1 = 0)
    (hbv : b 0 * v 0 + b 1 * v 1 = 0)
    (hbMv : b 0 * (M 0 0 * v 0 + M 0 1 * v 1) +
      b 1 * (M 1 0 * v 0 + M 1 1 * v 1) = 0)
    (hEuler : ∀ i : Fin 2, d * U i = x 0 * M (i.castAdd 2) 0 +
      x 1 * M (i.castAdd 2) 1 + z * M (i.castAdd 2) 2 + w * M (i.castAdd 2) 3) :
    x 0 * U 1 = x 1 * U 0 := by
  have hcross : x 0 * v 1 = x 1 * v 0 :=
    binary_covector_common_kernel_cross_equation b x (fun i => v (i.castAdd 2)) hb hx hbx hbv
  have hv0 : v 0 ≠ 0 := by
    intro hz
    have hv1 : v 1 = 0 := (mul_eq_zero.mp (by simpa only [hz, mul_zero] using hcross)).resolve_left hx
    apply hv
    funext i
    fin_cases i <;> assumption
  have hbMx : b 0 * (M 0 0 * x 0 + M 0 1 * x 1) +
      b 1 * (M 1 0 * x 0 + M 1 1 * x 1) = 0 := by
    apply mul_left_cancel₀ hv0
    linear_combination x 0 * hbMv - (b 0 * M 0 1 + b 1 * M 1 1) * hcross
  have he0 := hEuler 0
  have he1 := hEuler 1
  have hcast0 : (0 : Fin 2).castAdd 2 = (0 : Fin 4) := by decide
  have hcast1 : (1 : Fin 2).castAdd 2 = (1 : Fin 4) := by decide
  simp only [hcast0, hcast1] at he0 he1
  simp only [hcol2, hcol3] at he0 he1
  have hbU : b 0 * U 0 + b 1 * U 1 = 0 := by
    apply mul_left_cancel₀ hd
    linear_combination b 0 * he0 + b 1 * he1 + hbMx + (z * q - w * p) * hbv
  exact binary_covector_common_kernel_cross_equation b x U hb hx hbx hbU

end DimensionFourDependence
