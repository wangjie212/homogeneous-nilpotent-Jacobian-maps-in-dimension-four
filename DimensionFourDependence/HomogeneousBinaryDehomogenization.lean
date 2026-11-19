import DimensionFourDependence.HomogenizedParameterPencil

/-! # Homogeneous binary forms construct bounded univariate parameter polynomials -/

namespace DimensionFourDependence

open MvPolynomial

set_option maxHeartbeats 2500000

variable {K : Type*} [Field K]

/-- Dehomogenizing a homogeneous binary form gives a univariate
polynomial of degree at most the same degree, and homogenizing it back
recovers the entire original binary form. -/
theorem homogeneous_binary_form_constructs_bounded_univariate_parameter
    (F : MvPolynomial (Fin 2) K) {N : ℕ} (hF : F.IsHomogeneous N) :
    ∃ v : Polynomial K, v.natDegree ≤ N ∧ v.homogenize N = F := by
  classical
  let v : Polynomial K := aeval ![Polynomial.X, 1] F
  have hexpand : v = ∑ d ∈ F.support, Polynomial.C (F.coeff d) * Polynomial.X ^ (d 0) := by
    change aeval ![Polynomial.X, 1] F = _
    conv_lhs => rw [F.as_sum]
    simp only [map_sum, aeval_monomial]
    apply Finset.sum_congr rfl
    intro d _hd
    change Polynomial.C (F.coeff d) * d.prod (fun i k => ![Polynomial.X, 1] i ^ k) = _
    congr 1
    rw [Finsupp.prod_fintype]
    · simp [Fin.prod_univ_two]
    · intro i
      simp
  have hdegree : v.natDegree ≤ N := by
    apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
    intro k hk
    rw [hexpand, Polynomial.finsetSum_coeff]
    apply Finset.sum_eq_zero
    intro d hd
    have hdN : d 0 + d 1 = N := by
      have he := hF (mem_support_iff.mp hd)
      simpa [Finsupp.weight_apply, Finsupp.sum_fintype, Fin.sum_univ_two] using he
    have hne : d 0 ≠ k := by omega
    simp [Polynomial.coeff_C_mul_X_pow, hne, Ne.symm hne]
  exact ⟨v, hdegree, Polynomial.homogenize_eq_of_isHomogeneous hF rfl⟩

end DimensionFourDependence
