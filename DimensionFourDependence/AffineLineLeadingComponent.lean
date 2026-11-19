import DimensionFourDependence.HomogeneousAffineLeadingCoefficient

/-! # A polynomial's top homogeneous component on an affine line -/

namespace DimensionFourDependence

open MvPolynomial

set_option maxHeartbeats 1500000

variable {K E σ : Type*} [Field K] [Field E] [Algebra K E]

/-- The top allowed coefficient of any polynomial on an affine line
depends only on its top homogeneous component and the line's direction. -/
theorem affine_line_coefficient_at_totalDegree
    (p : MvPolynomial σ K) (u v : σ → E) :
    (aeval (fun i => Polynomial.C (u i) + Polynomial.C (v i) * Polynomial.X) p).coeff p.totalDegree =
      aeval v (homogeneousComponent p.totalDegree p) := by
  let s : σ → Polynomial E := fun i => Polynomial.C (u i) + Polynomial.C (v i) * Polynomial.X
  let d := p.totalDegree
  have hs (i : σ) : (s i).natDegree ≤ 1 := by
    apply Polynomial.natDegree_add_le_of_degree_le (by simp)
    exact Polynomial.natDegree_mul_le.trans (by simpa using (Polynomial.natDegree_X_le (R := E)))
  have hp : aeval s p = ∑ i ∈ Finset.range (d + 1), aeval s (homogeneousComponent i p) := by
    rw [← map_sum, sum_homogeneousComponent]
  change (aeval s p).coeff d = _
  rw [hp, Polynomial.finsetSum_coeff, Finset.sum_range_succ]
  have hl : (∑ i ∈ Finset.range d, (aeval s (homogeneousComponent i p)).coeff d) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    apply Polynomial.coeff_eq_zero_of_natDegree_lt
    exact ((polynomial_natDegree_aeval_le_totalDegree s hs (homogeneousComponent i p)).trans
      (homogeneousComponent_isHomogeneous i p).totalDegree_le).trans_lt (Finset.mem_range.mp hi)
  rw [hl, zero_add]
  change (aeval s (homogeneousComponent d p)).coeff d = aeval v (homogeneousComponent d p)
  exact homogeneous_affine_line_coefficient_at_degree (homogeneousComponent d p)
    (homogeneousComponent_isHomogeneous d p) u v

end DimensionFourDependence
