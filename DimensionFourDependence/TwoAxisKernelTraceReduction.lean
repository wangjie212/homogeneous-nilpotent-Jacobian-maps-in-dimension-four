import DimensionFourDependence.InvariantVectorTraceConstraints

/-! # The two original nilpotent mixed traces reduce to the binary Wronskian equations -/

namespace DimensionFourDependence

open Matrix

variable {F : Type*} [Field F]

set_option maxHeartbeats 2500000

/-- The Jacobian shape of a direction (0,0,A(x,y),B(x,y)). -/
def twoAxisDirectionJacobian (a b : Fin 2 → F) : Matrix (Fin 4) (Fin 4) F :=
  Matrix.of ![![0, 0, 0, 0], ![0, 0, 0, 0], ![a 0, a 1, 0, 0], ![b 0, b 1, 0, 0]]

/-- The first mixed trace keeps exactly the original binary Wronskian. -/
theorem two_axis_kernel_first_trace_identity
    (M : Matrix (Fin 4) (Fin 4) F) (a b : Fin 2 → F) (p q : F) (v : Fin 4 → F)
    (hcol2 : ∀ i, M i 2 = q * v i) (hcol3 : ∀ i, M i 3 = -p * v i) :
    Matrix.trace (M * twoAxisDirectionJacobian a b) =
      (q * a 0 - p * b 0) * v 0 + (q * a 1 - p * b 1) * v 1 := by
  simp [Matrix.trace, Matrix.mul_apply, Fin.sum_univ_succ, twoAxisDirectionJacobian, hcol2, hcol3]
  ring

/-- The second mixed trace retains the first-row derivative term and
an explicit multiple of the first mixed trace. -/
theorem two_axis_kernel_second_trace_identity
    (M : Matrix (Fin 4) (Fin 4) F) (a b : Fin 2 → F) (p q : F) (v : Fin 4 → F)
    (hcol2 : ∀ i, M i 2 = q * v i) (hcol3 : ∀ i, M i 3 = -p * v i) :
    Matrix.trace (M ^ 2 * twoAxisDirectionJacobian a b) =
      (q * a 0 - p * b 0) * (M 0 0 * v 0 + M 0 1 * v 1) +
      (q * a 1 - p * b 1) * (M 1 0 * v 0 + M 1 1 * v 1) +
      (q * v 2 - p * v 3) * ((q * a 0 - p * b 0) * v 0 + (q * a 1 - p * b 1) * v 1) := by
  simp [pow_two, Matrix.trace, Matrix.mul_apply, Fin.sum_univ_succ,
    twoAxisDirectionJacobian, hcol2, hcol3]
  ring

/-- A nonzero second component of the classified direction constructs
the derivative vector and both actual Wronskian annihilation equations.
No invariant-coordinate factorization or reduced matrix nilpotence is supplied. -/
theorem two_axis_kernel_traces_construct_binary_derivative_constraints
    (M : Matrix (Fin 4) (Fin 4) F) (a b : Fin 2 → F) (p q : F) (hq : q ≠ 0)
    (hkernel : ∀ i, p * M i 2 + q * M i 3 = 0)
    (htrace : Matrix.trace (M * twoAxisDirectionJacobian a b) = 0)
    (htrace2 : Matrix.trace (M ^ 2 * twoAxisDirectionJacobian a b) = 0) :
    ∃ v : Fin 4 → F, (∀ i, M i 2 = q * v i) ∧ (∀ i, M i 3 = -p * v i) ∧
      (q * a 0 - p * b 0) * v 0 + (q * a 1 - p * b 1) * v 1 = 0 ∧
      (q * a 0 - p * b 0) * (M 0 0 * v 0 + M 0 1 * v 1) +
        (q * a 1 - p * b 1) * (M 1 0 * v 0 + M 1 1 * v 1) = 0 := by
  let v : Fin 4 → F := fun i => M i 2 / q
  have hcol2 (i : Fin 4) : M i 2 = q * v i := by dsimp [v]; field_simp [hq]
  have hcol3 (i : Fin 4) : M i 3 = -p * v i := by
    have he := hkernel i
    rw [hcol2] at he
    apply (mul_left_cancel₀ hq)
    linear_combination he
  rw [two_axis_kernel_first_trace_identity M a b p q v hcol2 hcol3] at htrace
  rw [two_axis_kernel_second_trace_identity M a b p q v hcol2 hcol3, htrace, mul_zero, add_zero] at htrace2
  exact ⟨v, hcol2, hcol3, htrace, htrace2⟩

end DimensionFourDependence
