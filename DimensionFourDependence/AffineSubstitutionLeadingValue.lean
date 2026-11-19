import DimensionFourDependence.AffineLineLeadingComponent
import DimensionFourDependence.AffineSubstitutionDegree

/-! # Highest-degree values after restriction to affine coordinates -/

namespace DimensionFourDependence

open MvPolynomial

variable {L A σ ι : Type*} [Field L] [Field A] [Algebra L A]

/-- The coefficient at an allowed degree after a linear-in-parameter
substitution is evaluation of the corresponding homogeneous component. -/
theorem aeval_degree_bounded_coefficient_eq_homogeneous_value
    (p : MvPolynomial σ L) {d : ℕ} (hd : p.totalDegree ≤ d)
    (s : σ → Polynomial A) (hs : ∀ i, (s i).natDegree ≤ 1) :
    (aeval s p).coeff d = aeval (fun i => (s i).coeff 1) (homogeneousComponent d p) := by
  rcases lt_or_eq_of_le hd with hlt | he
  · rw [Polynomial.coeff_eq_zero_of_natDegree_lt
      ((polynomial_natDegree_aeval_le_totalDegree s hs p).trans_lt hlt),
      homogeneousComponent_eq_zero d p hlt, map_zero]
  subst d
  let d := p.totalDegree
  have hsum : aeval s p = ∑ i ∈ Finset.range (d + 1), aeval s (homogeneousComponent i p) := by
    rw [← map_sum, sum_homogeneousComponent]
  conv_lhs => rw [hsum, Polynomial.finsetSum_coeff, Finset.sum_range_succ]
  have hl : (∑ i ∈ Finset.range d, (aeval s (homogeneousComponent i p)).coeff d) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    apply Polynomial.coeff_eq_zero_of_natDegree_lt
    exact ((polynomial_natDegree_aeval_le_totalDegree s hs _).trans
      (homogeneousComponent_isHomogeneous i p).totalDegree_le).trans_lt (Finset.mem_range.mp hi)
  rw [hl, zero_add]
  exact homogeneous_aeval_coefficient_at_degree _ (homogeneousComponent_isHomogeneous d p) s hs

private theorem direction_polynomial_degree_le_one (a : A) :
    (Polynomial.C a * Polynomial.X).natDegree ≤ 1 :=
  Polynomial.natDegree_mul_le.trans (by simp)

/-- Any direction that annihilates the leading part of a divisor also
annihilates the highest allowed homogeneous part of the dividend. -/
theorem homogeneous_value_eq_zero_of_divisor_direction
    (P Q : MvPolynomial σ L) (hP : P ≠ 0) (hPQ : P ∣ Q) {d : ℕ}
    (hd : Q.totalDegree ≤ d) (e : σ → A)
    (he : aeval e (homogeneousComponent P.totalDegree P) = 0) :
    aeval e (homogeneousComponent d Q) = 0 := by
  by_cases hQ : Q = 0
  · simp [hQ]
  obtain ⟨B, rfl⟩ := hPQ
  let z : σ → Polynomial A := fun i => Polynomial.C (e i) * Polynomial.X
  have hz (i : σ) : (z i).natDegree ≤ 1 := direction_polynomial_degree_le_one _
  have hz1 : (fun i => (z i).coeff 1) = e := by
    funext i
    simp [z]
  have hdeg := totalDegree_mul_of_isDomain hP (right_ne_zero_of_mul hQ)
  have hBd : B.totalDegree ≤ d - P.totalDegree := by omega
  have hPz := polynomial_natDegree_aeval_le_totalDegree z hz P
  have hBz := (polynomial_natDegree_aeval_le_totalDegree z hz B).trans hBd
  have hp := aeval_degree_bounded_coefficient_eq_homogeneous_value P le_rfl z hz
  rw [hz1, he] at hp
  have hQz := aeval_degree_bounded_coefficient_eq_homogeneous_value (P * B) hd z hz
  have hsum : P.totalDegree + (d - P.totalDegree) = d := by omega
  rw [map_mul, ← hsum, Polynomial.coeff_mul_add_eq_of_natDegree_le hPz hBz,
    hp, zero_mul, hsum, hz1] at hQz
  exact hQz.symm

/-- The top value after substituting affine coordinates uses just the
linear part of the substituted coordinates. -/
theorem affine_substitution_homogeneous_value
    (g : σ → MvPolynomial ι L) (hg : ∀ i, (g i).totalDegree ≤ 1)
    (p : MvPolynomial σ L) {d : ℕ} (hd : p.totalDegree ≤ d) (e : ι → A) :
    aeval e (homogeneousComponent d (aeval g p)) =
      aeval (fun i => aeval e (homogeneousComponent 1 (g i))) (homogeneousComponent d p) := by
  let z : ι → Polynomial A := fun i => Polynomial.C (e i) * Polynomial.X
  have hz (i : ι) : (z i).natDegree ≤ 1 := direction_polynomial_degree_le_one _
  have hz1 : (fun i => (z i).coeff 1) = e := by
    funext i
    simp [z]
  have hgs (i : σ) : (aeval z (g i)).natDegree ≤ 1 :=
    (polynomial_natDegree_aeval_le_totalDegree z hz _).trans (hg i)
  have hdeg := (totalDegree_aeval_le_of_affine g hg p).trans hd
  rw [← hz1, ← aeval_degree_bounded_coefficient_eq_homogeneous_value _ hdeg z hz,
    hz1, comp_aeval_apply, aeval_degree_bounded_coefficient_eq_homogeneous_value p hd _ hgs]
  have hpoint : (fun i => (aeval z (g i)).coeff 1) =
      fun i => aeval e (homogeneousComponent 1 (g i)) := by
    funext i
    rw [aeval_degree_bounded_coefficient_eq_homogeneous_value _ (hg i) z hz, hz1]
  rw [hpoint]

end DimensionFourDependence
