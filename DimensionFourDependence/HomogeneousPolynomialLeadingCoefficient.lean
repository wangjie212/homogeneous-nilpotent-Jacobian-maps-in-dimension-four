import DimensionFourDependence.HomogeneousAffineLeadingCoefficient

/-! # The highest allowed coefficient under polynomial substitution

Uniform polynomial degree bounds multiply the homogeneous degree.
The coefficient there is the original form evaluated on the highest
allowed coefficients, including when individual degrees drop.
-/

namespace DimensionFourDependence

open MvPolynomial

variable {K E sigma : Type*} [Field K] [CommRing E] [Algebra K E]

/-- At any uniform polynomial degree bound, the highest allowed
coefficient of a homogeneous form is its value on the coefficient
direction. No exact-degree or nonvanishing condition is needed. -/
theorem homogeneous_aeval_coefficient_at_scaled_degree
    (P : MvPolynomial sigma K) {D : ℕ} (hP : P.IsHomogeneous D)
    (s : sigma → Polynomial E) (m : ℕ) (hs : ∀ i, (s i).natDegree ≤ m) :
    (aeval s P).coeff (m * D) = aeval (fun i => (s i).coeff m) P := by
  classical
  conv_lhs => rw [P.as_sum, map_sum]
  conv_rhs => rw [P.as_sum, map_sum]
  rw [Polynomial.finsetSum_coeff]
  apply Finset.sum_congr rfl
  intro d hd
  rw [aeval_monomial, aeval_monomial, Polynomial.algebraMap_apply, Polynomial.coeff_C_mul]
  rw [hP.degree_eq_sum_deg_support hd]
  congr 1
  change (∏ i ∈ d.support, s i ^ d i).coeff (m * ∑ i ∈ d.support, d i) =
    ∏ i ∈ d.support, ((s i).coeff m) ^ d i
  rw [Finset.mul_sum]
  rw [polynomial_product_coefficient_at_sum_bound d.support (fun i => s i ^ d i)
    (fun i => m * d i) (fun i _ => by
      simpa only [Nat.mul_comm] using Polynomial.natDegree_pow_le_of_le (d i) (hs i))]
  apply Finset.prod_congr rfl
  intro i _
  simpa only [Nat.mul_comm] using Polynomial.coeff_pow_of_natDegree_le (m := d i) (hs i)

end DimensionFourDependence
