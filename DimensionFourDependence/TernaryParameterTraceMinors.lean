import DimensionFourDependence.TernaryClosedPolynomialParameter
import DimensionFourDependence.PolynomialParameterTraceSpecialization
import DimensionFourDependence.AffineConeTrace

/-! # Nilpotent trace and minors on the common-parameter chart -/

namespace DimensionFourDependence

open MvPolynomial Matrix

universe u
set_option maxHeartbeats 2300000

variable {K : Type u} [Field K] [CharZero K]
local notation "R₃" => MvPolynomial (Fin 3) K

/-- Normalization and independence force independence of the two
ordinary derivatives in the common-parameter description. -/
theorem ternary_parameter_derivatives_independent
    (H : Fin 3 → R₃) (hind : ¬ ComponentsDependent H)
    (r : R₃) (f g : Polynomial K) (hf₀ : f.eval 0 = 0) (hg₀ : g.eval 0 = 0)
    (hf : H 0 = Polynomial.aeval r f) (hg : H 2 = Polynomial.aeval r g)
    (a b : K) (he : Polynomial.C a * f.derivative + Polynomial.C b * g.derivative = 0) :
    a = 0 ∧ b = 0 := by
  let p := Polynomial.C a * f + Polynomial.C b * g
  have hp : p.derivative = 0 := by
    simpa only [p, Polynomial.derivative_add, Polynomial.derivative_C_mul] using he
  have hp₀ : p.eval 0 = 0 := by simp [p, hf₀, hg₀]
  have hzero : p = 0 := by
    have hC := Polynomial.eq_C_of_derivative_eq_zero hp
    nth_rw 1 [hC] at hp₀
    rw [Polynomial.eval_C] at hp₀
    rw [hC, hp₀, map_zero]
  have hv : C a * H 0 + C b * H 2 = 0 := by
    rw [hf, hg]
    simpa only [p, map_add, map_mul, Polynomial.aeval_C, algebraMap_eq, map_zero] using
      congrArg (Polynomial.aeval r) hzero
  by_contra h
  apply hind
  refine ⟨![a, 0, b], ?_, ?_⟩
  · intro hz
    exact h ⟨congrFun hz 0, congrFun hz 2⟩
  · rw [Fin.sum_univ_three]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      zero_smul, add_zero, smul_eq_C_mul]
    exact hv

/-- The trace and sum of principal two-by-two minors on `[f(r), v, g(r)]`. -/
theorem ternary_common_parameter_trace_and_minors
    (H : Fin 3 → R₃) (hN : IsNilpotent (jac H))
    (r : R₃) (f g : Polynomial K)
    (hf : H 0 = Polynomial.aeval r f) (hg : H 2 = Polynomial.aeval r g) :
    let v := H 1
    let U := Polynomial.aeval r f.derivative
    let V := Polynomial.aeval r g.derivative
    let W := U * pderiv 0 r + V * pderiv 2 r
    W + pderiv 1 v = 0 ∧
      W * pderiv 1 v - pderiv 1 r * (U * pderiv 0 v + V * pderiv 2 v) = 0 := by
  let u := fun j : Fin 3 => pderiv j r
  let w := fun j : Fin 3 => pderiv j (H 1)
  let U := Polynomial.aeval r f.derivative
  let V := Polynomial.aeval r g.derivative
  let J : Matrix (Fin 3) (Fin 3) R₃ := of ![fun j => U * u j, w, fun j => V * u j]
  have hJ : jac H = J := by
    funext i j
    fin_cases i
    · change pderiv j (H 0) = U * u j
      rw [hf]
      simpa only [U, u, smul_eq_mul, mul_comm] using (pderiv (R := K) j).map_aeval f r
    · rfl
    · change pderiv j (H 2) = V * u j
      rw [hg]
      simpa only [V, u, smul_eq_mul, mul_comm] using (pderiv (R := K) j).map_aeval g r
  have hn : IsNilpotent J := hJ ▸ hN
  have ht := (Matrix.isNilpotent_trace_of_isNilpotent hn).eq_zero
  have ht₂ := (Matrix.isNilpotent_trace_of_isNilpotent (hn.pow_of_pos (by decide : (2 : ℕ) ≠ 0))).eq_zero
  have ht' : U * u 0 + w 1 + V * u 2 = 0 := by
    change ∑ i, J i i = 0 at ht
    rw [Fin.sum_univ_three] at ht
    exact ht
  have h₁ : U * u 0 + V * u 2 + w 1 = 0 := by linear_combination ht'
  have he : J.trace ^ 2 - (J ^ 2).trace =
      2 * ((U * u 0 + V * u 2) * w 1 - u 1 * (U * w 0 + V * w 2)) := by
    rw [pow_two J]
    simp only [trace, diag, mul_apply, Fin.sum_univ_three]
    change (U * u 0 + w 1 + V * u 2) ^ 2 -
      (U * u 0 * (U * u 0) + U * u 1 * w 0 + U * u 2 * (V * u 0) +
        (w 0 * (U * u 1) + w 1 * w 1 + w 2 * (V * u 1)) +
        (V * u 0 * (U * u 2) + V * u 1 * w 2 + V * u 2 * (V * u 2))) = _
    ring
  rw [ht, ht₂, zero_pow (by decide : (2 : ℕ) ≠ 0), sub_self] at he
  exact ⟨h₁, (mul_eq_zero.mp he.symm).resolve_left two_ne_zero⟩

/-- The source variable in the middle must genuinely occur in the
common parameter of the first and last outputs. -/
theorem ternary_common_parameter_middle_partial_ne_zero
    (r v : R₃) (f g : Polynomial K) (hr : 0 < r.totalDegree)
    (hind : ∀ a b : K, Polynomial.C a * f.derivative + Polynomial.C b * g.derivative = 0 →
      a = 0 ∧ b = 0)
    (ht : Polynomial.aeval r f.derivative * pderiv 0 r +
      Polynomial.aeval r g.derivative * pderiv 2 r + pderiv 1 v = 0)
    (hm : (Polynomial.aeval r f.derivative * pderiv 0 r +
      Polynomial.aeval r g.derivative * pderiv 2 r) * pderiv 1 v -
      pderiv 1 r * (Polynomial.aeval r f.derivative * pderiv 0 v +
        Polynomial.aeval r g.derivative * pderiv 2 v) = 0) : pderiv 1 r ≠ 0 := by
  intro hy
  rw [hy, zero_mul, sub_zero] at hm
  have hv : pderiv 1 v = 0 := by
    rcases mul_eq_zero.mp hm with h | h
    · simpa only [h, zero_add] using ht
    · exact h
  let A : Fin 3 → Polynomial K := ![f.derivative, 0, g.derivative]
  have ht' : ∑ i, Polynomial.aeval r (A i) * pderiv i r = 0 := by
    rw [Fin.sum_univ_three]
    change Polynomial.aeval r f.derivative * pderiv 0 r +
      Polynomial.aeval r 0 * pderiv 1 r + Polynomial.aeval r g.derivative * pderiv 2 r = 0
    simpa only [map_zero, zero_mul, add_zero, hv] using ht
  have hc (m : Fin 3 →₀ ℕ) :
      (pderiv 0 r).coeff m = 0 ∧ (pderiv 2 r).coeff m = 0 := by
    apply hind
    apply Polynomial.eq_zero_of_infinite_isRoot
    apply Set.infinite_univ.mono
    intro t _
    have he := polynomial_parameter_trace_specializes_globally r hr A ht' t
    rw [Fin.sum_univ_three] at he
    change C (f.derivative.eval t) * pderiv 0 r + C ((0 : Polynomial K).eval t) * pderiv 1 r +
      C (g.derivative.eval t) * pderiv 2 r = 0 at he
    simp only [Polynomial.eval_zero, map_zero, zero_mul, add_zero] at he
    have hs := congrArg (fun P : R₃ => P.coeff m) he
    change (C _ * pderiv 0 r + C _ * pderiv 2 r : R₃).coeff m = (0 : R₃).coeff m at hs
    simp only [AddMonoidAlgebra.coeff_add, Finsupp.add_apply, coeff_C_mul,
      AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply] at hs
    change (_ + _ : Polynomial K).eval t = 0
    simpa only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, mul_comm] using hs
  have hAll (i : Fin 3) : pderiv i r = 0 := by
    fin_cases i
    · ext m
      simpa using (hc m).1
    · exact hy
    · ext m
      simpa using (hc m).2
  have hC := polynomial_all_partials_zero_eq_constant r hAll
  have hz := congrArg totalDegree hC
  rw [totalDegree_C] at hz
  omega

end DimensionFourDependence
