import DimensionFourDependence.TernaryBilinearTraceMinor
import DimensionFourDependence.TernaryBilinearOneMovingOutput
import DimensionFourDependence.TernaryConstantRightKernelDependence

/-! # A nonzero mixed product cannot be a third independent nilpotent output -/

namespace DimensionFourDependence

open MvPolynomial Matrix

universe u
set_option maxHeartbeats 2250000

variable {K : Type u} [Field K] [CharZero K]
local notation "R₃" => MvPolynomial (Fin 3) K
local notation "R₂" => MvPolynomial (Fin 2) K

/-- The exact trace and principal minors rule out the bilinear chart
obtained from two distinct directions of the generic conic. -/
theorem normalized_independent_ternary_nilpotent_bilinear_output_impossible
    (H : Fin 3 → R₃) (h0 : ∀ i, aeval (fun _ : Fin 3 => (0 : K)) (H i) = 0)
    (hind : ¬ComponentsDependent H) (hN : IsNilpotent (jac H))
    (γ a b c : K) (hγ : γ ≠ 0)
    (h : H 2 = C γ * H 0 * H 1 + C a * H 0 + C b * H 1 + C c) :
    False := by
  obtain ⟨ht, hMu, hMv⟩ := ternary_bilinear_output_nilpotent_trace_and_minors H γ a b c hN h
  let e := ternaryLastVariableEquiv (K := K)
  let U := e (H 0)
  let V := e (H 1)
  have hn (i : Fin 3) : H i ≠ 0 := (linearIndependent_of_componentsIndependent H hind).ne_zero i
  by_cases hU : U.natDegree = 0
  · have hzU : pderiv 2 (H 0) = 0 := ternary_last_degree_zero_pderiv_last_eq_zero (H 0) hU
    by_cases hV : V.natDegree = 0
    · have hzV : pderiv 2 (H 1) = 0 := ternary_last_degree_zero_pderiv_last_eq_zero (H 1) hV
      have hzW : pderiv 2 (H 2) = 0 := by
        rw [h]
        simp only [map_add, pderiv_mul, pderiv_C, hzU, hzV, mul_zero, zero_mul, add_zero]
      let z : Fin 3 → K := ![0,0,1]
      have hz : z ≠ 0 := by
        intro he
        exact one_ne_zero (congrFun he (2 : Fin 3))
      have hzero (i : Fin 3) : pderiv 2 (H i) = 0 := by
        fin_cases i
        · exact hzU
        · exact hzV
        · exact hzW
      have hker : jac H *ᵥ (fun i => C (z i)) = 0 := by
        funext i
        simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, jac, z, hzero]
      exact hind (normalized_ternary_nilpotent_constant_right_kernel_componentsDependent H h0 hN z hz hker)
    · exact ternary_bilinear_minor_one_moving_output_impossible (H 0) (H 1) 1 0 (by decide)
        (h0 0) (hn 0) hU (Nat.pos_of_ne_zero hV) γ a hγ (hMu hzU)
  · by_cases hV : V.natDegree = 0
    · have hzV : pderiv 2 (H 1) = 0 := ternary_last_degree_zero_pderiv_last_eq_zero (H 1) hV
      exact ternary_bilinear_minor_one_moving_output_impossible (H 1) (H 0) 0 1 (by decide)
        (h0 1) (hn 1) hV (Nat.pos_of_ne_zero hU) γ b hγ (hMv hzV)
    · have hEval := congrArg e ht
      change e (pderiv (0 : Fin 2).castSucc (H 0) + pderiv (1 : Fin 2).castSucc (H 1) +
        (C γ * H 1 + C a) * pderiv (Fin.last 2) (H 0) +
        (C γ * H 0 + C b) * pderiv (Fin.last 2) (H 1)) = e 0 at hEval
      simp only [map_add, map_mul, map_zero] at hEval
      have heZ (i : Fin 3) : e (pderiv (Fin.last 2) (H i)) = (e (H i)).derivative :=
        ternaryLastVariableEquiv_last_pderiv (H i)
      have heXY (i : Fin 3) (j : Fin 2) : e (pderiv j.castSucc (H i)) =
          ternaryCoefficientPartial j (e (H i)) := ternaryLastVariableEquiv_active_pderiv j (H i)
      have hc (d : K) : e (C d) = Polynomial.C (C d) := ternaryLastVariableEquiv_C d
      rw [heXY 0 0, heXY 1 1, heZ 0, heZ 1, hc γ, hc a, hc b] at hEval
      apply bilinear_trace_both_last_degrees_positive_impossible U V
        (Nat.pos_of_ne_zero hU) (Nat.pos_of_ne_zero hV) γ a b hγ
      rw [Polynomial.derivative_mul]
      change ternaryCoefficientPartial 0 U + ternaryCoefficientPartial 1 V +
        (Polynomial.C (C γ) * V + Polynomial.C (C a)) * U.derivative +
        (Polynomial.C (C γ) * U + Polynomial.C (C b)) * V.derivative = 0 at hEval
      linear_combination hEval

end DimensionFourDependence
