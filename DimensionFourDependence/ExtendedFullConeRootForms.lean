import DimensionFourDependence.FixedVertexScaledOutputSpan
import DimensionFourDependence.RulingFormNonvanishing

/-! # Full cone root forms retain the original coefficient field

The root and actual output point may lie in a larger field. The forms
are nevertheless constructed in the original coefficient field itself.
The actual extended output proves the second form is nonzero on the
original ruling, and its fourth axis separates it from the first form.
-/

namespace DimensionFourDependence

open Matrix

set_option maxHeartbeats 2000000

variable {E G : Type*} [Field E] [Field G] [Algebra E G] {m : ℕ}

/-- A full cone presentation at an extended ruling point constructs
independent root forms over the same original coefficients, retaining
the original numerator and the exact linear input level. -/
theorem extended_full_cone_constructs_root_forms_over_same_coefficients
    (A : Matrix (Fin m) (Fin 4) E) (y : Fin 4 → G)
    (hy : A.map (algebraMap E G) *ᵥ y = 0)
    (haxis : A *ᵥ (Fin.snoc (0 : Fin 3 → E) 1 : Fin 4 → E) = 0)
    {d : ℕ} (hd : 0 < d) (R : G) (hR : R ≠ 0) (V : Fin 3 → E) (hV : V ≠ 0)
    (a b : E) (ell : G) (hb : b ≠ 0)
    (hfirst : ∀ i : Fin 3, y i.castSucc = algebraMap E G (V i) * R ^ d)
    (hlast : y (Fin.last 3) = algebraMap E G a * R ^ d + algebraMap E G b * R ^ (d - 1) * ell)
    (N : Fin 4 → E) (hNlast : N (Fin.last 3) = 0)
    (hNy : (fun i => algebraMap E G (N i)) ⬝ᵥ y ≠ 0) :
    ∃ M S : Fin 4 → E, M (Fin.last 3) ≠ 0 ∧ S (Fin.last 3) = 0 ∧
      ((fun i => algebraMap E G (M i)) ⬝ᵥ y) * R =
        ((fun i => algebraMap E G (N i)) ⬝ᵥ y) * ell ∧
      (fun i => algebraMap E G (S i)) ⬝ᵥ y = R ^ d ∧
      LinearIndependent E ![rulingFormRestriction (LinearMap.ker A.toLin') M,
        rulingFormRestriction (LinearMap.ker A.toLin') S] := by
  classical
  obtain ⟨j, hj⟩ : ∃ j : Fin 3, V j ≠ 0 := by
    simpa only [ne_eq, funext_iff, Pi.zero_apply, not_forall] using hV
  let S : Fin 4 → E := fun i => if i = j.castSucc then (V j)⁻¹ else 0
  let axis : Fin 4 → E := Fin.snoc (0 : Fin 3 → E) 1
  let k : E := ∑ i : Fin 3, N i.castSucc * V i
  let M : Fin 4 → E := (k / b) • (axis - a • S)
  let B (q : Fin 4 → E) : Fin 4 → G := fun i => algebraMap E G (q i)
  have hSlast : S (Fin.last 3) = 0 := by
    change (if Fin.last 3 = j.castSucc then (V j)⁻¹ else 0) = 0
    split_ifs with h
    · exact False.elim ((Fin.castSucc_ne_last j) h.symm)
    · rfl
  have hjG : algebraMap E G (V j) ≠ 0 := (map_ne_zero (algebraMap E G)).mpr hj
  have hSvalue : B S ⬝ᵥ y = R ^ d := by
    have hBS : B S = (fun i => if i = j.castSucc then (algebraMap E G (V j))⁻¹ else 0) := by
      funext i
      by_cases hi : i = j.castSucc <;> simp [B, S, hi]
    rw [hBS]
    simp [dotProduct, hfirst, hjG]
  have hNvalue : B N ⬝ᵥ y = algebraMap E G k * R ^ d := by
    change (∑ i : Fin 4, algebraMap E G (N i) * y i) = _
    rw [Fin.sum_univ_castSucc]
    change (∑ i : Fin 3, algebraMap E G (N i.castSucc) * y i.castSucc) +
      algebraMap E G (N (Fin.last 3)) * y (Fin.last 3) = _
    rw [hNlast, map_zero, zero_mul, add_zero]
    simp_rw [hfirst]
    simp only [k, map_sum, map_mul, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hk : k ≠ 0 := by
    intro hzero
    exact hNy (by rw [hNvalue, hzero, map_zero, zero_mul])
  have haxis_pair (q : Fin 4 → E) : q ⬝ᵥ axis = q (Fin.last 3) := by
    change (∑ i : Fin 4, q i * axis i) = q (Fin.last 3)
    rw [Fin.sum_univ_castSucc]
    change (∑ i : Fin 3, q i.castSucc * axis i.castSucc) + q (Fin.last 3) * axis (Fin.last 3) = _
    simp only [axis, Fin.snoc_castSucc, Pi.zero_apply, mul_zero, Finset.sum_const_zero,
      Fin.snoc_last, mul_one, zero_add]
  have haxis_y : B axis ⬝ᵥ y = y (Fin.last 3) := by
    change (∑ i : Fin 4, algebraMap E G (axis i) * y i) = _
    rw [Fin.sum_univ_castSucc]
    change (∑ i : Fin 3, algebraMap E G (axis i.castSucc) * y i.castSucc) +
      algebraMap E G (axis (Fin.last 3)) * y (Fin.last 3) = _
    simp only [axis, Fin.snoc_castSucc, Pi.zero_apply, map_zero, zero_mul, Finset.sum_const_zero,
      Fin.snoc_last, map_one, one_mul, zero_add]
  have hMlast : M (Fin.last 3) = k / b := by
    simp only [M, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, axis, Fin.snoc_last, hSlast,
      mul_zero, sub_zero, mul_one]
  have hBM : B M = algebraMap E G (k / b) • (B axis - algebraMap E G a • B S) := by
    funext i
    simp only [B, M, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, map_mul, map_sub]
  have hbG : algebraMap E G b ≠ 0 := (map_ne_zero (algebraMap E G)).mpr hb
  have hMvalue : B M ⬝ᵥ y = algebraMap E G k * R ^ (d - 1) * ell := by
    rw [hBM, smul_dotProduct, sub_dotProduct, smul_dotProduct, haxis_y, hSvalue, hlast]
    simp only [smul_eq_mul, map_div₀]
    field_simp [hbG]
    ring
  have hroot : (B M ⬝ᵥ y) * R = (B N ⬝ᵥ y) * ell := by
    have hpow : R ^ (d - 1) * R = R ^ d := by rw [← pow_succ]; congr 1; omega
    rw [hMvalue, hNvalue]
    calc
      _ = algebraMap E G k * (R ^ (d - 1) * R) * ell := by ring
      _ = _ := by rw [hpow]
  have hSnonzero : rulingFormRestriction (LinearMap.ker A.toLin') S ≠ 0 :=
    ruling_form_ne_zero_of_extended_value_ne_zero A S y hy
      (by rw [hSvalue]; exact pow_ne_zero d hR)
  refine ⟨M, S, ?_, hSlast, hroot, hSvalue, ?_⟩
  · rw [hMlast]
    exact div_ne_zero hk hb
  · exact dual_pair_independent_of_separating_vector _ _ ⟨axis, haxis⟩
      (by change M ⬝ᵥ axis ≠ 0; rw [haxis_pair, hMlast]; exact div_ne_zero hk hb)
      hSnonzero (by change S ⬝ᵥ axis = 0; rw [haxis_pair, hSlast])

end DimensionFourDependence
