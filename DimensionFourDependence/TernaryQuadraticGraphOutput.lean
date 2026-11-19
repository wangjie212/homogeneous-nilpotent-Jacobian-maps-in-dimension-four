import DimensionFourDependence.TernaryParameterQuadraticPotential
import DimensionFourDependence.ConstantKernelSourceReduction

/-! # The exact output formula on a quadratic graph parameter -/

namespace DimensionFourDependence

open MvPolynomial Matrix

universe u
set_option maxHeartbeats 3000000

variable {K : Type u} [Field K] [CharZero K]
local notation "R₃" => MvPolynomial (Fin 3) K
local notation "R₂" => MvPolynomial (Fin 2) K

omit [CharZero K] in
/-- Evaluation at the zero level of the quadratic graph fixes all
horizontal polynomials and sends the parameter itself to zero. -/
theorem ternary_quadratic_graph_zero_level_evaluation (Q : R₂) :
    let s : Fin 3 → R₂ := ![X 0, X 1, Q]
    (∀ B : R₂, aeval s (rename Fin.castSucc B) = B) ∧
      aeval s (X 2 - rename Fin.castSucc Q) = 0 := by
  let s : Fin 3 → R₂ := ![X 0, X 1, Q]
  have h : ∀ B : R₂, aeval s (rename Fin.castSucc B) = B := by
    intro B
    rw [aeval_rename]
    have hs : s ∘ Fin.castSucc = X := by funext i; fin_cases i <;> rfl
    rw [hs, aeval_X_left, AlgHom.id_apply]
  refine ⟨h, ?_⟩
  rw [map_sub, h Q, aeval_X]
  exact sub_self Q

omit [CharZero K] in
/-- An ordinary polynomial evaluated at a zero level reduces to its
original scalar value at zero. -/
theorem map_ordinary_parameter_value_at_zero
    {E : Type*} [CommRing E] [Algebra K E] {A : Type*} [CommRing A] [Algebra K A]
    (e : A →ₐ[K] E) (r : A) (hr : e r = 0) (f : Polynomial K) :
    e (Polynomial.aeval r f) = algebraMap K E (f.eval 0) := by
  rw [← Polynomial.aeval_algHom_apply e r f, hr]
  rw [← Polynomial.coeff_zero_eq_aeval_zero', Polynomial.coeff_zero_eq_eval_zero]

/-- The trace determines the full middle output from the graph
gradient and the affine middle output on the zero level. -/
theorem ternary_quadratic_graph_trace_determines_middle_output
    (Q : R₂) (f g a b c : Polynomial K)
    (hf₀ : f.eval 0 = 0) (hg₀ : g.eval 0 = 0)
    (v : R₃)
    (hv : v = Polynomial.aeval (X 2 - rename Fin.castSucc Q) a * X 1 +
      Polynomial.aeval (X 2 - rename Fin.castSucc Q) b * X 0 +
      Polynomial.aeval (X 2 - rename Fin.castSucc Q) c)
    (ht : pderiv 0 (Polynomial.aeval (X 2 - rename Fin.castSucc Q) f) +
      pderiv 1 (Polynomial.aeval (X 2 - rename Fin.castSucc Q) g) + pderiv 2 v = 0) :
    v = rename Fin.castSucc (pderiv (0 : Fin 2) Q) * Polynomial.aeval (X 2 - rename Fin.castSucc Q) f +
      rename Fin.castSucc (pderiv (1 : Fin 2) Q) * Polynomial.aeval (X 2 - rename Fin.castSucc Q) g +
      (C (a.eval 0) * X 1 + C (b.eval 0) * X 0 + C (c.eval 0)) := by
  let r := X 2 - rename Fin.castSucc Q
  let F := Polynomial.aeval r f
  let G := Polynomial.aeval r g
  let U := rename Fin.castSucc (pderiv (0 : Fin 2) Q)
  let V := rename Fin.castSucc (pderiv (1 : Fin 2) Q)
  let w := v - (U * F + V * G)
  have hu : pderiv 2 U = 0 := binary_rename_vertex_pderiv_zero _
  have hV : pderiv 2 V = 0 := binary_rename_vertex_pderiv_zero _
  have hF : pderiv 0 F + U * pderiv 2 F = 0 := (quadratic_graph_polynomial_gradient_lifts_invariant Q f).1
  have hG : pderiv 1 G + V * pderiv 2 G = 0 := (quadratic_graph_polynomial_gradient_lifts_invariant Q g).2
  have hw : pderiv 2 w = 0 := by
    change pderiv 2 (v - (U * F + V * G)) = 0
    simp only [map_sub, map_add, pderiv_mul, hu, hV]
    change pderiv 0 F + pderiv 1 G + pderiv 2 v = 0 at ht
    linear_combination ht - hF - hG
  obtain ⟨L, hL⟩ := zero_last_partial_constructs_smaller_source_polynomial w hw
  let s : Fin 3 → R₂ := ![X 0, X 1, Q]
  obtain ⟨hs, hr⟩ := ternary_quadratic_graph_zero_level_evaluation Q
  change ∀ B : R₂, aeval s (rename Fin.castSucc B) = B at hs
  change aeval s r = 0 at hr
  have hFL : aeval s F = 0 := by
    change aeval s (Polynomial.aeval r f) = _
    rw [map_ordinary_parameter_value_at_zero _ r hr, hf₀, map_zero]
  have hGL : aeval s G = 0 := by
    change aeval s (Polynomial.aeval r g) = _
    rw [map_ordinary_parameter_value_at_zero _ r hr, hg₀, map_zero]
  have hVval : aeval s v = C (a.eval 0) * X 1 + C (b.eval 0) * X 0 + C (c.eval 0) := by
    rw [hv]
    change aeval s (Polynomial.aeval r a * X 1 + Polynomial.aeval r b * X 0 + Polynomial.aeval r c) = _
    simp only [map_add, map_mul, map_ordinary_parameter_value_at_zero _ r hr, algebraMap_eq, aeval_X]
    rfl
  have hLv : L = aeval s v := by
    have he := congrArg (aeval s) hL
    rw [hs] at he
    change L = aeval s (v - (U * F + V * G)) at he
    simpa only [map_sub, map_add, map_mul, hFL, hGL, mul_zero, add_zero, sub_zero] using he
  rw [hVval] at hLv
  rw [hLv] at hL
  simp only [map_add, map_mul, rename_C, rename_X] at hL
  change C (a.eval 0) * X (1 : Fin 3) + C (b.eval 0) * X (0 : Fin 3) + C (c.eval 0) =
    v - (U * F + V * G) at hL
  change v = U * F + V * G + (C (a.eval 0) * X 1 + C (b.eval 0) * X 0 + C (c.eval 0))
  linear_combination -hL

end DimensionFourDependence
