import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Data.Fin.VecNotation

/-! # The one-direction and two-direction cases of a binary quadratic form -/

namespace DimensionFourDependence

open Matrix

variable {E : Type*} [Field E]

/-- Evaluation of a symmetric binary quadratic form with diagonal
entries `a,c` and off-diagonal entry `b`. -/
def binaryQuadraticValue (a b c : E) (e : Fin 2 → E) : E :=
  a * e 0 ^ 2 + 2 * b * e 0 * e 1 + c * e 1 ^ 2

/-- A degenerate binary quadratic form has an explicit nonzero
direction over its own coefficient field. -/
theorem binaryQuadratic_degenerate_constructs_direction
    (a b c : E) (hdet : a * c - b ^ 2 = 0) :
    ∃ e : Fin 2 → E, e ≠ 0 ∧ binaryQuadraticValue a b c e = 0 := by
  by_cases ha : a = 0
  · refine ⟨![1,0], ?_, by simp [binaryQuadraticValue, ha]⟩
    intro h
    exact one_ne_zero (congrFun h (0 : Fin 2))
  · refine ⟨![-b,a], ?_, ?_⟩
    · intro h
      exact ha (congrFun h (1 : Fin 2))
    · change a * (-b) ^ 2 + 2 * b * (-b) * a + c * a ^ 2 = 0
      linear_combination a * hdet

variable [CharZero E] [IsAlgClosed E]

/-- A nondegenerate binary quadratic form has two independent zero
directions over a closed field. The determinant displayed here is the
determinant of their two representatives. -/
theorem binaryQuadratic_nondegenerate_constructs_two_directions
    (a b c : E) (hdet : a * c - b ^ 2 ≠ 0) :
    ∃ e f : Fin 2 → E, e 0 * f 1 - e 1 * f 0 ≠ 0 ∧
      binaryQuadraticValue a b c e = 0 ∧ binaryQuadraticValue a b c f = 0 := by
  by_cases ha : a = 0
  · have hb : b ≠ 0 := by intro h; apply hdet; simp [ha,h]
    have h2b : 2 * b ≠ 0 := mul_ne_zero two_ne_zero hb
    refine ⟨![1,0], ![-c,2 * b], ?_, by simp [binaryQuadraticValue, ha], ?_⟩
    · simpa using h2b
    · simp only [binaryQuadraticValue, head_cons, tail_cons]
      change a * (-c) ^ 2 + 2 * b * (-c) * (2 * b) + c * (2 * b) ^ 2 = 0
      rw [ha, zero_mul, zero_add]
      ring
  · obtain ⟨r, hr⟩ := IsAlgClosed.exists_pow_nat_eq (b ^ 2 - a * c) (n := 2) (by decide)
    have hr0 : r ≠ 0 := by
      intro h
      rw [h, zero_pow (by decide)] at hr
      exact hdet (sub_eq_zero.mpr (sub_eq_zero.mp hr.symm).symm)
    let s := (-b + r) / a
    let t := (-b - r) / a
    have hs : a * s + b = r := by dsimp [s]; field_simp; ring
    have ht : a * t + b = -r := by dsimp [t]; field_simp; ring
    have hroot (v : E) (hv : (a * v + b) ^ 2 = r ^ 2) : a * v ^ 2 + 2 * b * v + c = 0 := by
      apply (mul_eq_zero.mp ?_).resolve_left ha
      calc
        a * (a * v ^ 2 + 2 * b * v + c) = (a * v + b) ^ 2 - (b ^ 2 - a * c) := by ring
        _ = 0 := by rw [hv, hr, sub_self]
    refine ⟨![s,1], ![t,1], ?_, ?_, ?_⟩
    · change s * 1 - 1 * t ≠ 0
      simp only [mul_one, one_mul]
      intro h
      have he : s = t := sub_eq_zero.mp h
      rw [he, ht] at hs
      have hm : (2 : E) * r = 0 := by linear_combination -hs
      exact (mul_ne_zero two_ne_zero hr0) hm
    · have hv : a * s ^ 2 + 2 * b * s + c = 0 := hroot s (by rw [hs])
      simpa [binaryQuadraticValue] using hv
    · have hv : a * t ^ 2 + 2 * b * t + c = 0 := hroot t (by rw [ht, neg_sq])
      simpa [binaryQuadraticValue] using hv

end DimensionFourDependence
