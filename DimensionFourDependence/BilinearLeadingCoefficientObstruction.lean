import DimensionFourDependence.AffineTriangularDivisibility

/-! # A leading product has higher source degree than these partials -/

namespace DimensionFourDependence

open MvPolynomial

set_option maxHeartbeats 1200000

variable {K : Type*} [Field K] {n : ℕ}
local notation "R₀" => MvPolynomial (Fin n) K

/-- The two lower-degree derivative terms cannot cancel the product of
the nonzero leading coefficients. This includes a missing derivative term. -/
theorem nonzero_leading_product_ne_negative_partial_sum
    (A B : R₀) (hA : A ≠ 0) (hB : B ≠ 0)
    (u v : R₀) (hu : u = 0 ∨ u = A) (hv : v = 0 ∨ v = B)
    (i j : Fin n) (c : K) (hc : c ≠ 0) :
    pderiv i u + pderiv j v + C c * A * B ≠ 0 := by
  intro h
  have hC : (C c : R₀) ≠ 0 := C_ne_zero.mpr hc
  have hprod : C c * A * B ≠ 0 := mul_ne_zero (mul_ne_zero hC hA) hB
  have he : pderiv i u + pderiv j v = -(C c * A * B) := by
    linear_combination h
  have hyp (Q P : R₀) (hq : Q = 0 ∨ Q = P) (k : Fin n) (hz : pderiv k Q ≠ 0) :
      (pderiv k Q).totalDegree + 1 ≤ P.totalDegree := by
    rcases hq with rfl | rfl
    · exact (hz (map_zero _)).elim
    · exact nonzero_polynomial_partial_totalDegree_succ_le _ k hz
  have hpos : 0 < A.totalDegree + B.totalDegree := by
    by_contra hp
    by_cases hi : pderiv i u = 0
    · by_cases hj : pderiv j v = 0
      · rw [hi, hj, zero_add, zero_add] at h
        exact hprod h
      · have hdeg := hyp v B hv j hj
        omega
    · have hdeg := hyp u A hu i hi
      omega
  have hi : (pderiv i u).totalDegree < A.totalDegree + B.totalDegree := by
    by_cases hz : pderiv i u = 0
    · rwa [hz, totalDegree_zero]
    · have hdeg := hyp u A hu i hz
      omega
  have hj : (pderiv j v).totalDegree < A.totalDegree + B.totalDegree := by
    by_cases hz : pderiv j v = 0
    · rwa [hz, totalDegree_zero]
    · have hdeg := hyp v B hv j hz
      omega
  have hlt := (totalDegree_add (pderiv i u) (pderiv j v)).trans_lt (max_lt hi hj)
  have hd : (C c * A * B).totalDegree = A.totalDegree + B.totalDegree := by
    rw [totalDegree_mul_of_isDomain (mul_ne_zero hC hA) hB,
      totalDegree_mul_of_isDomain hC hA, totalDegree_C, zero_add]
  rw [he, totalDegree_neg, hd] at hlt
  exact (lt_irrefl _) hlt

end DimensionFourDependence
