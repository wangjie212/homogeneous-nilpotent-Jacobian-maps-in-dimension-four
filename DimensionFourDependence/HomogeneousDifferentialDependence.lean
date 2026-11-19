import DimensionFourDependence.ImageEquationWitness

/-! # The homogeneous differential dependence step in Proposition 2.3

Euler contraction changes a nonzero polynomial relation between the
differentials of two forms of the same positive degree into a constant
linear relation between the forms.
-/

namespace DimensionFourDependence

open MvPolynomial

variable {K σ : Type*} [Field K] [CharZero K] [Fintype σ]

/-- Euler contraction of a polynomial relation between two differentials. -/
theorem homogeneous_differential_relation_euler
    (f g a b : MvPolynomial σ K) {d : ℕ} (hd : 0 < d)
    (hf : f.IsHomogeneous d) (hg : g.IsHomogeneous d)
    (hgrad : ∀ k, a * pderiv k f + b * pderiv k g = 0) : a * f + b * g = 0 := by
  have he : d • (a * f + b * g) = 0 := by
    rw [nsmul_add, ← mul_smul_comm, ← mul_smul_comm,
      ← hf.sum_X_mul_pderiv, ← hg.sum_X_mul_pderiv,
      Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_eq_zero
    intro k _
    linear_combination X k * hgrad k
  exact (smul_eq_zero.mp he).resolve_left (by omega)

/-- A differential relation for two equal positive-degree forms supplies
a nonzero constant relation, including the cases of zero components. -/
theorem constant_relation_of_homogeneous_differential_relation
    (f g a b : MvPolynomial σ K) {d : ℕ} (hd : 0 < d)
    (hf : f.IsHomogeneous d) (hg : g.IsHomogeneous d)
    (hab : a ≠ 0 ∨ b ≠ 0)
    (hgrad : ∀ k, a * pderiv k f + b * pderiv k g = 0) :
    ∃ c t : K, (c ≠ 0 ∨ t ≠ 0) ∧ c • f + t • g = 0 := by
  by_cases hf0 : f = 0
  · exact ⟨1, 0, Or.inl one_ne_zero, by simp [hf0]⟩
  have he := homogeneous_differential_relation_euler f g a b hd hf hg hgrad
  have hb : b ≠ 0 := by
    intro hb
    have ha : a = 0 := by
      apply (mul_eq_zero.mp (by simpa only [hb, zero_mul, add_zero] using he)).resolve_right hf0
    exact hab.elim (fun h => h ha) (fun h => h hb)
  have hW (k : σ) : f * pderiv k g = g * pderiv k f := by
    have hz : b * (f * pderiv k g - g * pderiv k f) = 0 := by
      linear_combination f * hgrad k - pderiv k f * he
    exact sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left hb)
  obtain ⟨c, hc⟩ := proportional_of_wronskian hf hg hf0 hW
  exact ⟨-c, 1, Or.inr one_ne_zero, by simp [hc]⟩

end DimensionFourDependence
