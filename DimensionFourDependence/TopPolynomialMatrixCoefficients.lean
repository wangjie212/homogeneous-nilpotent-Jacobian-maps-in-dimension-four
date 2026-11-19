import DimensionFourDependence.Homogeneous

/-! # The top coefficient of a power of a polynomial matrix -/

namespace DimensionFourDependence

open MvPolynomial Matrix

variable {R ι : Type*} [CommRing R] [Fintype ι] [DecidableEq ι]

/-- A common degree bound lets the top coefficient of a matrix power
be computed by taking the corresponding matrix power of top coefficients. -/
theorem polynomial_matrix_power_top_coefficient
    (M : Matrix ι ι (Polynomial R)) (d : ℕ) (hM : ∀ i j, (M i j).natDegree ≤ d)
    (k : ℕ) (i j : ι) :
    ((M ^ k) i j).natDegree ≤ k * d ∧
    ((M ^ k) i j).coeff (k * d) = ((M.map fun f => f.coeff d) ^ k) i j := by
  classical
  induction k generalizing i j with
  | zero =>
    simp only [pow_zero, zero_mul, Matrix.one_apply]
    by_cases h : i = j <;> simp [h]
  | succ k ih =>
    rw [pow_succ, pow_succ, Nat.succ_mul, Matrix.mul_apply, Matrix.mul_apply]
    refine ⟨?_, ?_⟩
    · apply Polynomial.natDegree_sum_le_of_forall_le
      intro l _
      exact (Polynomial.natDegree_mul_le).trans (Nat.add_le_add (ih i l).1 (hM l j))
    · rw [Polynomial.finsetSum_coeff]
      apply Finset.sum_congr rfl
      intro l _
      rw [Polynomial.coeff_mul_add_eq_of_natDegree_le (ih i l).1 (hM l j),
        (ih i l).2, Matrix.map_apply]

variable {K σ : Type*} [Field K]

theorem gradeHom_natDegree_le_of_totalDegree (p : MvPolynomial σ K) {d : ℕ}
    (hp : p.totalDegree ≤ d) : (gradeHom p).natDegree ≤ d := by
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro k hk
  rw [coeff_gradeHom]
  exact homogeneousComponent_eq_zero k p (hp.trans_lt hk)

/-- Nilpotence of an arbitrary polynomial matrix descends to the matrix
of homogeneous components at a common upper degree bound. -/
theorem top_homogeneous_component_matrix_isNilpotent
    (M : Matrix ι ι (MvPolynomial σ K)) (d : ℕ)
    (hM : ∀ i j, (M i j).totalDegree ≤ d) (hN : IsNilpotent M) :
    IsNilpotent (M.map (homogeneousComponent d)) := by
  let φ := (gradeHom (σ := σ) (K := K)).toRingHom
  let P := φ.mapMatrix M
  have hP (i j : ι) : (P i j).natDegree ≤ d := gradeHom_natDegree_le_of_totalDegree _ (hM i j)
  obtain ⟨k, hk⟩ : IsNilpotent P := hN.map φ.mapMatrix
  refine ⟨k, ?_⟩
  have hmap : (P.map fun f => f.coeff d) = M.map (homogeneousComponent d) := by
    funext i j
    exact coeff_gradeHom (M i j) d
  rw [← hmap]
  funext i j
  have he := (polynomial_matrix_power_top_coefficient P d hP k i j).2
  rw [hk] at he
  simpa using he.symm

end DimensionFourDependence
