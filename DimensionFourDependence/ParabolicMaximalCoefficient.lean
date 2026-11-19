import DimensionFourDependence.HomogeneousAffineLeadingCoefficient

/-! # The maximal candidate coefficient of a polynomial invariant on a parabola

The actual finite vertex support supplies a maximal candidate degree.
A positive vertex index makes it positive. Constancy then makes the
sum of all tied highest contributions zero; terms of smaller degree
are removed using their individual bounds.
-/

namespace DimensionFourDependence

variable {E : Type*} [Field E]

/-- A positive vertex index makes the actual largest candidate degree
positive, even when its coefficient's degree has dropped by multiplicity. -/
theorem parabolic_candidate_degree_exists_maximum
    (s : Finset ℕ) (d : ℕ → ℕ) (hpositive : ∃ j ∈ s, 0 < j) :
    ∃ N : ℕ, 0 < N ∧ (∀ j ∈ s, d j + j * 2 ≤ N) ∧
      ∃ j ∈ s, d j + j * 2 = N := by
  obtain ⟨j, hj, hjpos⟩ := hpositive
  obtain ⟨k, hk, hmax⟩ := s.exists_max_image (fun i => d i + i * 2) ⟨j, hj⟩
  exact ⟨d k + k * 2, lt_of_lt_of_le (by omega : 0 < d j + j * 2) (hmax j hj),
    hmax, k, hk, rfl⟩

/-- Constancy retains exactly the contributions tied at the largest
positive candidate degree after the quadratic vertex substitution. -/
theorem constant_parabolic_sum_maximal_coefficient
    (s : Finset ℕ) (f : ℕ → Polynomial E) (d : ℕ → ℕ)
    (hf : ∀ j ∈ s, (f j).natDegree ≤ d j)
    (w : Polynomial E) (hw : w.natDegree ≤ 2)
    (N : ℕ) (hN : 0 < N) (hmax : ∀ j ∈ s, d j + j * 2 ≤ N)
    (a : E) (hconstant : (∑ j ∈ s, f j * w ^ j) = Polynomial.C a) :
    (∑ j ∈ s.filter (fun j => d j + j * 2 = N), (f j).coeff (d j) * w.coeff 2 ^ j) = 0 := by
  classical
  have hterm (j : ℕ) (hj : j ∈ s) :
      (f j * w ^ j).coeff N =
        if d j + j * 2 = N then (f j).coeff (d j) * w.coeff 2 ^ j else 0 := by
    by_cases he : d j + j * 2 = N
    · rw [if_pos he, ← he, Polynomial.coeff_mul_add_eq_of_natDegree_le (hf j hj)
        (Polynomial.natDegree_pow_le_of_le j hw), Polynomial.coeff_pow_of_natDegree_le hw]
    · rw [if_neg he]
      have hdeg : (f j * w ^ j).natDegree ≤ d j + j * 2 :=
        Polynomial.natDegree_mul_le.trans
          (Nat.add_le_add (hf j hj) (Polynomial.natDegree_pow_le_of_le j hw))
      exact Polynomial.coeff_eq_zero_of_natDegree_lt (hdeg.trans_lt (by have := hmax j hj; omega))
  have he := congrArg (fun p : Polynomial E => p.coeff N) hconstant
  rw [Polynomial.finsetSum_coeff, Polynomial.coeff_C_of_ne_zero (by omega : N ≠ 0)] at he
  rw [Finset.sum_filter]
  exact (Finset.sum_congr rfl hterm).symm.trans he

end DimensionFourDependence
