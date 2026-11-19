import DimensionFourDependence.GraphRulingCovectorProjection
import Mathlib.FieldTheory.AlgebraicClosure

/-! # The complete cone formula constructs independent ruling root forms

Use a nonzero directrix coordinate to recover the root power. A second
covector subtracts that coordinate from the last output. A nonzero
canonical numerator fixes its scale. The actual fourth axis separates
the two forms on the original ruling, and every constructed coefficient
remains algebraic over the same coefficient field.
-/

namespace DimensionFourDependence

open Matrix

set_option maxHeartbeats 2000000

variable {C E : Type*} [Field C] [Field E] [Algebra C E]

/-- The original full cone output values, a nonzero numerator and
the actual ruling's fourth axis construct the independent root forms.
No pair of forms, dual vectors or independence condition is supplied. -/
theorem full_cone_constructs_independent_algebraic_ruling_root_forms
    (W : Submodule E (Fin 4 → E)) (y : Fin 4 → E) (hy : y ∈ W)
    (haxis : (Fin.snoc (0 : Fin 3 → E) 1 : Fin 4 → E) ∈ W)
    {d : ℕ} (hd : 0 < d) (R : E) (hR : R ≠ 0) (V : Fin 3 → E) (hV : V ≠ 0)
    (a b ell : E) (hb : b ≠ 0)
    (hValg : ∀ i, IsAlgebraic C (V i)) (haalg : IsAlgebraic C a) (hbalg : IsAlgebraic C b)
    (hfirst : ∀ i : Fin 3, y i.castSucc = V i * R ^ d)
    (hlast : y (Fin.last 3) = a * R ^ d + b * R ^ (d - 1) * ell)
    (N : Fin 4 → E) (hNalg : ∀ i, IsAlgebraic C (N i))
    (hNlast : N (Fin.last 3) = 0) (hNy : N ⬝ᵥ y ≠ 0) :
    ∃ M S : Fin 4 → E, (∀ i, IsAlgebraic C (M i)) ∧ (∀ i, IsAlgebraic C (S i)) ∧
      M (Fin.last 3) ≠ 0 ∧ S (Fin.last 3) = 0 ∧
      (M ⬝ᵥ y) * R = (N ⬝ᵥ y) * ell ∧ S ⬝ᵥ y = R ^ d ∧
      LinearIndependent E ![rulingFormRestriction W M, rulingFormRestriction W S] := by
  classical
  obtain ⟨j, hj⟩ : ∃ j : Fin 3, V j ≠ 0 := by
    simpa only [ne_eq, funext_iff, Pi.zero_apply, not_forall] using hV
  let S : Fin 4 → E := fun i => if i = j.castSucc then (V j)⁻¹ else 0
  let axis : Fin 4 → E := Fin.snoc (0 : Fin 3 → E) 1
  let k : E := ∑ i : Fin 3, N i.castSucc * V i
  let M : Fin 4 → E := (k / b) • (axis - a • S)
  have hSlast : S (Fin.last 3) = 0 := by
    change (if Fin.last 3 = j.castSucc then (V j)⁻¹ else 0) = 0
    split_ifs with h
    · exact False.elim ((Fin.castSucc_ne_last j) h.symm)
    · rfl
  have hSvalue : S ⬝ᵥ y = R ^ d := by
    simp [S, dotProduct, hfirst, hj]
  have hNvalue : N ⬝ᵥ y = k * R ^ d := by
    change (∑ i : Fin 4, N i * y i) = k * R ^ d
    rw [Fin.sum_univ_castSucc]
    change (∑ i : Fin 3, N i.castSucc * y i.castSucc) + N (Fin.last 3) * y (Fin.last 3) = k * R ^ d
    rw [hNlast, zero_mul, add_zero]
    simp_rw [hfirst]
    dsimp only [k]
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hk : k ≠ 0 := by
    intro hzero
    exact hNy (by rw [hNvalue, hzero, zero_mul])
  have haxis_pair (q : Fin 4 → E) : q ⬝ᵥ axis = q (Fin.last 3) := by
    change (∑ i : Fin 4, q i * axis i) = q (Fin.last 3)
    rw [Fin.sum_univ_castSucc]
    change (∑ i : Fin 3, q i.castSucc * axis i.castSucc) + q (Fin.last 3) * axis (Fin.last 3) = q (Fin.last 3)
    simp only [axis, Fin.snoc_castSucc, Pi.zero_apply, mul_zero, Finset.sum_const_zero,
      Fin.snoc_last, mul_one, zero_add]
  have hMlast : M (Fin.last 3) = k / b := by
    simp only [M, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, axis, Fin.snoc_last, hSlast,
      mul_zero, sub_zero, mul_one]
  have hMvalue : M ⬝ᵥ y = k * R ^ (d - 1) * ell := by
    rw [show M = (k / b) • (axis - a • S) from rfl, smul_dotProduct, sub_dotProduct, smul_dotProduct]
    rw [dotProduct_comm axis y, haxis_pair y, hSvalue, hlast]
    simp only [smul_eq_mul]
    field_simp [hb]
    ring
  have hroot : (M ⬝ᵥ y) * R = (N ⬝ᵥ y) * ell := by
    have hpow : R ^ (d - 1) * R = R ^ d := by
      rw [← pow_succ]
      congr 1
      omega
    rw [hMvalue, hNvalue]
    calc
      _ = k * (R ^ (d - 1) * R) * ell := by ring
      _ = _ := by rw [hpow]
  let A := algebraicClosure C E
  have hSmem (i : Fin 4) : S i ∈ A := by
    by_cases hi : i = j.castSucc
    · rw [show S i = (V j)⁻¹ by simp [S, hi]]
      exact A.inv_mem (mem_algebraicClosure_iff.mpr (hValg j))
    · rw [show S i = 0 by simp [S, hi]]
      exact A.zero_mem
  have hkmem : k ∈ A := by
    exact A.sum_mem (fun i _ => A.mul_mem (mem_algebraicClosure_iff.mpr (hNalg i.castSucc))
      (mem_algebraicClosure_iff.mpr (hValg i)))
  have hMmem (i : Fin 4) : M i ∈ A := by
    have hax : axis i ∈ A := by
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simpa only [axis, Fin.snoc_last] using A.one_mem
      · simpa only [axis, Fin.snoc_castSucc, Pi.zero_apply] using A.zero_mem
    exact A.mul_mem (A.div_mem hkmem (mem_algebraicClosure_iff.mpr hbalg))
      (A.sub_mem hax (A.mul_mem (mem_algebraicClosure_iff.mpr haalg) (hSmem i)))
  refine ⟨M, S, (fun i => mem_algebraicClosure_iff.mp (hMmem i)),
    (fun i => mem_algebraicClosure_iff.mp (hSmem i)), ?_, hSlast, hroot, hSvalue, ?_⟩
  · rw [hMlast]
    exact div_ne_zero hk hb
  · rw [LinearIndependent.pair_iff]
    intro u v huv
    have he := LinearMap.congr_fun huv ⟨axis, haxis⟩
    change u * (M ⬝ᵥ axis) + v * (S ⬝ᵥ axis) = 0 at he
    rw [haxis_pair, haxis_pair, hMlast, hSlast, mul_zero, add_zero] at he
    have hu : u = 0 := (mul_eq_zero.mp he).resolve_right (div_ne_zero hk hb)
    have he' := LinearMap.congr_fun huv ⟨y, hy⟩
    change u * (M ⬝ᵥ y) + v * (S ⬝ᵥ y) = 0 at he'
    rw [hu, zero_mul, zero_add, hSvalue] at he'
    exact ⟨hu, (mul_eq_zero.mp he').resolve_right (pow_ne_zero d hR)⟩

end DimensionFourDependence
