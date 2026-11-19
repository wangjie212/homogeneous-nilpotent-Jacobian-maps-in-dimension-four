import DimensionFourDependence.PrimitiveParameterDenominator
import DimensionFourDependence.PolynomialParameterTraceSpecialization
import DimensionFourDependence.RationalParameterDerivation
import DimensionFourDependence.ReducedPencilVertexDifferential

/-! # A polynomial middle output has polynomial parameter coefficients -/

namespace DimensionFourDependence

open MvPolynomial

universe u
set_option maxHeartbeats 3200000

variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]
local notation "R₃" => MvPolynomial (Fin 3) K
local notation "F" => FractionRing R₃
local notation "ι" => (algebraMap R₃ F)

omit [CharZero K] [IsAlgClosed K] in
/-- A polynomial involving a variable cannot divide a nonzero
polynomial free of that variable. -/
theorem polynomial_divisor_degreeOf_le_of_ne_zero {n : ℕ}
    (i : Fin n) (p q : MvPolynomial (Fin n) K) (hq : q ≠ 0) (h : p ∣ q) :
    p.degreeOf i ≤ q.degreeOf i := by
  obtain ⟨s, rfl⟩ := h
  rw [degreeOf_mul_eq (left_ne_zero_of_mul hq) (right_ne_zero_of_mul hq)]
  exact Nat.le_add_right _ _

omit [CharZero K] [IsAlgClosed K] in
/-- A polynomial supported on coordinates other than `i` has zero
formal `i` derivative, directly by polynomial induction. -/
theorem pderiv_rename_eq_zero_of_outside_range {m n : ℕ}
    (j : Fin m → Fin n) (i : Fin n) (hj : ∀ k, j k ≠ i) (p : MvPolynomial (Fin m) K) :
    pderiv i (rename j p) = 0 := by
  induction p using MvPolynomial.induction_on with
  | C c => simp
  | add a b ha hb => simp only [map_add, ha, hb, add_zero]
  | mul_X a k ha => simp only [map_mul, rename_X, pderiv_mul, ha, pderiv_X_of_ne (hj k),
      zero_mul, mul_zero, add_zero]

/-- When an original polynomial source value is a horizontal form
with coefficients rational in a polynomial that depends on the middle
variable, every coefficient belongs to the ordinary parameter ring. -/
theorem ternary_horizontal_form_rational_coefficients_are_polynomial
    (r H : R₃) (hr : pderiv 1 r ≠ 0)
    (e : RatFunc K →ₐ[K] F) (he : e RatFunc.X = ι r)
    (P : MvPolynomial (Fin 2) (RatFunc K))
    (hP : eval₂ e.toRingHom (fun i => ι (X ((1 : Fin 3).succAbove i))) P = ι H) :
    ∃ Q : MvPolynomial (Fin 2) (Polynomial K),
      map (algebraMap (Polynomial K) (RatFunc K)) Q = P := by
  classical
  let j := (1 : Fin 3).succAbove
  let g := (Polynomial.aeval (R := K) r).toRingHom
  obtain ⟨D, hD, N, hN, hpole⟩ := parameter_form_reduced_common_denominator P
  have hCompat : e.toRingHom.comp (algebraMap (Polynomial K) (RatFunc K)) = (ι).comp g := by
    apply RingHom.ext
    intro p
    change e (algebraMap (Polynomial K) (RatFunc K) p) = ι (Polynomial.aeval r p)
    rw [rational_function_algHom_polynomial_value, he]
    exact Polynomial.aeval_algHom_apply (IsScalarTower.toAlgHom K R₃ F) r p
  have hCleared : eval₂Hom g (fun i => X (j i)) N = g D * H := by
    apply IsFractionRing.injective R₃ F
    have hx := congrArg (eval₂Hom e.toRingHom (fun i => ι (X (j i)))) hN
    change eval₂ e.toRingHom (fun i => ι (X (j i))) (map (algebraMap (Polynomial K) (RatFunc K)) N) =
      eval₂ e.toRingHom (fun i => ι (X (j i))) (C (algebraMap (Polynomial K) (RatFunc K) D) * P) at hx
    rw [eval₂_map, eval₂_mul, eval₂_C, hP, hCompat] at hx
    have hDvalue : e.toRingHom (algebraMap (Polynomial K) (RatFunc K) D) = ι (g D) :=
      DFunLike.congr_fun hCompat D
    rw [hDvalue] at hx
    rw [map_mul, map_eval₂Hom]
    exact hx
  have hDegree : D.natDegree = 0 := by
    by_contra h
    have hpos := Polynomial.natDegree_pos_iff_degree_pos.mp (Nat.pos_of_ne_zero h)
    obtain ⟨t, ht⟩ := IsAlgClosed.exists_root D hpos.ne'
    change D.eval t = 0 at ht
    let A : Ideal R₃ := Ideal.span {r - C t}
    let q := Ideal.Quotient.mk A
    have hCong : q.comp g = (q.comp C).comp (Polynomial.evalRingHom t) := by
      apply RingHom.ext
      intro L
      change q (Polynomial.aeval r L) = q (C (L.eval t))
      apply sub_eq_zero.mp
      rw [← map_sub]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton.mpr
        (polynomial_parameter_level_dvd_evaluation_difference r L t))
    have hSpecial : q (rename j (map (Polynomial.evalRingHom t) N)) = 0 := by
      have hx := congrArg q hCleared
      rw [map_eval₂Hom, hCong, map_mul] at hx
      have hz : q (g D) = 0 := by
        have hd := DFunLike.congr_fun hCong D
        simpa only [RingHom.comp_apply, Polynomial.coe_evalRingHom, ht, map_zero] using hd
      rw [hz, zero_mul] at hx
      rw [← hx]
      rw [rename_eq_aeval]
      change q (eval₂Hom C (X ∘ j) (map (Polynomial.evalRingHom t) N)) = _
      rw [map_eval₂Hom]
      simp only [coe_eval₂Hom, eval₂_map, RingHom.comp_assoc]
      rfl
    let W := rename j (map (Polynomial.evalRingHom t) N)
    have hW : W ≠ 0 := by
      simpa only [W, map_zero] using (rename_injective j (fun _ _ hz => Fin.succAbove_right_injective hz)).ne (hpole t ht)
    have hdiv : r - C t ∣ W := Ideal.mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp hSpecial)
    have hWdegree : W.degreeOf 1 = 0 := degreeOf_eq_zero_of_pderiv_eq_zero W 1
      (pderiv_rename_eq_zero_of_outside_range j 1 (fun i => Fin.succAbove_ne _ _) _)
    have hd := polynomial_divisor_degreeOf_le_of_ne_zero 1 _ W hW hdiv
    rw [hWdegree] at hd
    have hVars : (1 : Fin 3) ∉ (r - C t).vars := fun hm =>
      (mem_vars_iff_degreeOf_ne_zero.mp hm) (Nat.eq_zero_of_le_zero hd)
    have hp := pderiv_eq_zero_of_notMem_vars hVars
    rw [map_sub, pderiv_C, sub_zero] at hp
    exact hr hp
  have hC := Polynomial.eq_C_of_natDegree_eq_zero hDegree
  have hc : D.coeff 0 ≠ 0 := by intro hz; exact hD (by rw [hC, hz, map_zero])
  let S := Polynomial.C ((D.coeff 0)⁻¹)
  have hcancel : S * D = 1 := by
    calc
      S * D = S * Polynomial.C (D.coeff 0) := congrArg (fun w => S * w) hC
      _ = 1 := by rw [show S = Polynomial.C ((D.coeff 0)⁻¹) from rfl,
        ← map_mul, inv_mul_cancel₀ hc, map_one]
  refine ⟨C S * N, ?_⟩
  rw [map_mul, map_C, hN, ← mul_assoc, ← map_mul, ← map_mul, hcancel, map_one, map_one, one_mul]

end DimensionFourDependence
