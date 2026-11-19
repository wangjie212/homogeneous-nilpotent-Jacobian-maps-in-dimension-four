import DimensionFourDependence.TernaryGraphCrossIdentities
import DimensionFourDependence.Basic

/-! # Trace and principal-minor identities for the proposed bilinear output -/

namespace DimensionFourDependence

open MvPolynomial Matrix

universe u
set_option maxHeartbeats 1650000

variable {K : Type u} [Field K] [CharZero K]
local notation "R₃" => MvPolynomial (Fin 3) K

/-- The original Jacobian is exactly the graph matrix for a bilinear
last output, with no passage to a rational approximation. -/
theorem ternary_bilinear_output_jacobian
    (H : Fin 3 → R₃) (γ a b c : K)
    (h : H 2 = C γ * H 0 * H 1 + C a * H 0 + C b * H 1 + C c) :
    jac H =
      ternaryGraphMatrix (fun j => pderiv j (H 0)) (fun j => pderiv j (H 1))
        (C γ * H 1 + C a) (C γ * H 0 + C b) := by
  funext i j
  fin_cases i
  · rfl
  · rfl
  · change pderiv j (H 2) =
      (C γ * H 1 + C a) * pderiv j (H 0) + (C γ * H 0 + C b) * pderiv j (H 1)
    rw [h]
    simp only [map_add, pderiv_mul, pderiv_C, smul_eq_mul, mul_zero, add_zero]
    ring

/-- Nilpotence supplies the exact trace equation and the two reduced
principal-minor identities when one of the first two outputs is fixed
in the last source variable. -/
theorem ternary_bilinear_output_nilpotent_trace_and_minors
    (H : Fin 3 → R₃) (γ a b c : K) (hN : IsNilpotent (jac H))
    (h : H 2 = C γ * H 0 * H 1 + C a * H 0 + C b * H 1 + C c) :
    let u := fun j : Fin 3 => pderiv j (H 0)
    let v := fun j : Fin 3 => pderiv j (H 1)
    let p := C γ * H 1 + C a
    let q := C γ * H 0 + C b
    (u 0 + v 1 + p * u 2 + q * v 2 = 0) ∧
      (u 2 = 0 → u 0 ^ 2 + u 1 * (v 0 + p * v 2) = 0) ∧
      (v 2 = 0 → v 1 ^ 2 + v 0 * (u 1 + q * u 2) = 0) := by
  let u := fun j : Fin 3 => pderiv j (H 0)
  let v := fun j : Fin 3 => pderiv j (H 1)
  let p := C γ * H 1 + C a
  let q := C γ * H 0 + C b
  have hJ : IsNilpotent (ternaryGraphMatrix u v p q) :=
    (ternary_bilinear_output_jacobian H γ a b c h) ▸ hN
  have ht := (Matrix.isNilpotent_trace_of_isNilpotent hJ).eq_zero
  have ht₂ := (Matrix.isNilpotent_trace_of_isNilpotent (hJ.pow_of_pos (by decide : (2 : ℕ) ≠ 0))).eq_zero
  have hcross : ternaryCrossProduct u v 2 - p * ternaryCrossProduct u v 0 -
      q * ternaryCrossProduct u v 1 = 0 := by
    have he := ternaryGraphMatrix_trace_square_difference u v p q
    rw [ht, ht₂, zero_pow (by decide : (2 : ℕ) ≠ 0), sub_self] at he
    exact (mul_eq_zero.mp he.symm).resolve_left two_ne_zero
  have htr : u 0 + v 1 + p * u 2 + q * v 2 = 0 := by
    have he : trace (ternaryGraphMatrix u v p q) = u 0 + v 1 + p * u 2 + q * v 2 := by
      simp [ternaryGraphMatrix, trace, Matrix.diag, Fin.sum_univ_three, Pi.smul_apply, smul_eq_mul]
      ring
    exact he.symm.trans ht
  have hcross' : (u 0 * v 1 - u 1 * v 0) - p * (u 1 * v 2 - u 2 * v 1) -
      q * (u 2 * v 0 - u 0 * v 2) = 0 := hcross
  change (u 0 + v 1 + p * u 2 + q * v 2 = 0) ∧
    (u 2 = 0 → u 0 ^ 2 + u 1 * (v 0 + p * v 2) = 0) ∧
    (v 2 = 0 → v 1 ^ 2 + v 0 * (u 1 + q * u 2) = 0)
  refine ⟨htr, ?_, ?_⟩
  · intro hu
    rw [hu] at htr hcross'
    linear_combination (u 0) * htr - hcross'
  · intro hv
    rw [hv] at htr hcross'
    linear_combination (v 1) * htr - hcross'

end DimensionFourDependence
