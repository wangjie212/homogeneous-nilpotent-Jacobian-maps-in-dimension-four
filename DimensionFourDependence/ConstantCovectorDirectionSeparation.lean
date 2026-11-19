import DimensionFourDependence.SpecifiedCovectorPairFrame

/-! # Evaluation on a direction separates the two constant covectors -/

namespace DimensionFourDependence

open Matrix

universe u v
set_option maxHeartbeats 1500000

variable {K : Type u} {A : Type v} [Field K] [Field A] [Algebra K A] {n : ℕ}

/-- If one nonzero covector kills a direction while the other is
nonzero on it, the two covectors are linearly independent. -/
theorem constant_covectors_independent_of_separating_direction
    (l r : Fin n → K) (hl : l ≠ 0) (e : Fin n → A)
    (h₀ : ∑ i, algebraMap K A (l i) * e i = 0)
    (h₁ : ∑ i, algebraMap K A (r i) * e i ≠ 0) :
    LinearIndependent K (![l,r] : Fin 2 → (Fin n → K)) := by
  apply (LinearIndependent.pair_iff' hl).mpr
  intro c hc
  apply h₁
  rw [← hc]
  simp only [Pi.smul_apply, smul_eq_mul, map_mul, mul_assoc, ← Finset.mul_sum, h₀, mul_zero]

/-- A nonzero covector cannot vanish on both independent binary
directions, even after extension of its coefficient field. -/
theorem nonzero_binary_covector_cannot_kill_independent_directions
    (l : Fin 2 → K) (hl : l ≠ 0) (e f : Fin 2 → A)
    (hdet : e 0 * f 1 - e 1 * f 0 ≠ 0)
    (h₀ : algebraMap K A (l 0) * e 0 + algebraMap K A (l 1) * e 1 = 0) :
    algebraMap K A (l 0) * f 0 + algebraMap K A (l 1) * f 1 ≠ 0 := by
  intro h₁
  let a := algebraMap K A (l 0)
  let b := algebraMap K A (l 1)
  have ha : a * (e 0 * f 1 - e 1 * f 0) = 0 := by
    change a * e 0 + b * e 1 = 0 at h₀
    change a * f 0 + b * f 1 = 0 at h₁
    linear_combination (f 1) * h₀ - (e 1) * h₁
  have hb : b * (e 0 * f 1 - e 1 * f 0) = 0 := by
    change a * e 0 + b * e 1 = 0 at h₀
    change a * f 0 + b * f 1 = 0 at h₁
    linear_combination (e 0) * h₁ - (f 0) * h₀
  apply hl
  funext i
  fin_cases i
  · change l 0 = 0
    apply (algebraMap K A).injective
    simpa only [a, map_zero] using (mul_eq_zero.mp ha).resolve_right hdet
  · change l 1 = 0
    apply (algebraMap K A).injective
    simpa only [b, map_zero] using (mul_eq_zero.mp hb).resolve_right hdet

/-- A separating direction for binary covectors makes their row
matrix invertible over the original coefficient field. -/
theorem binary_row_matrix_det_ne_zero_of_separating_direction
    (l r : Fin 2 → K) (hl : l ≠ 0) (e : Fin 2 → A)
    (h₀ : algebraMap K A (l 0) * e 0 + algebraMap K A (l 1) * e 1 = 0)
    (h₁ : algebraMap K A (r 0) * e 0 + algebraMap K A (r 1) * e 1 ≠ 0) :
    (show Matrix (Fin 2) (Fin 2) K from ![l,r]).det ≠ 0 := by
  have hlin := constant_covectors_independent_of_separating_direction l r hl e
    (by simpa only [Fin.sum_univ_two] using h₀)
    (by simpa only [Fin.sum_univ_two] using h₁)
  have hUnit : IsUnit (show Matrix (Fin 2) (Fin 2) K from ![l,r]) :=
    Matrix.linearIndependent_rows_iff_isUnit.mp hlin
  exact isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det _).mp hUnit)

end DimensionFourDependence
