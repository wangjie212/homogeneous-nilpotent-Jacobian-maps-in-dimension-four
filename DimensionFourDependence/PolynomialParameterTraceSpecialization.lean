import DimensionFourDependence.AffineTriangularDivisibility
import Mathlib.Algebra.Polynomial.Div

/-! # Specialization of polynomial vector fields on a literal parameter level -/

namespace DimensionFourDependence

open MvPolynomial

variable {K : Type*} [Field K] {n : ℕ}

/-- Polynomial evaluation at a level is congruent to substitution of
the original scalar, modulo the literal polynomial defining the level. -/
theorem polynomial_parameter_level_dvd_evaluation_difference
    (P : MvPolynomial (Fin n) K) (A : Polynomial K) (t : K) :
    P - C t ∣ Polynomial.aeval P A - C (A.eval t) := by
  have h : Polynomial.X - Polynomial.C t ∣ A - Polynomial.C (A.eval t) := by
    rw [Polynomial.dvd_iff_isRoot, Polynomial.IsRoot.def, Polynomial.eval_sub,
      Polynomial.eval_C, sub_self]
  have he := map_dvd (Polynomial.aeval P).toRingHom h
  change Polynomial.aeval P (Polynomial.X - Polynomial.C t) ∣
    Polynomial.aeval P (A - Polynomial.C (A.eval t)) at he
  simpa only [map_sub, Polynomial.aeval_X, Polynomial.aeval_C, algebraMap_eq] using he

/-- A polynomial vector field with coefficients in one polynomial
parameter can be specialized to every constant level in its tangent
identity. Exact degree forces the specialized identity globally. -/
theorem polynomial_parameter_trace_specializes_globally
    (P : MvPolynomial (Fin n) K) (hP : 0 < P.totalDegree) (A : Fin n → Polynomial K)
    (h : ∑ i, Polynomial.aeval P (A i) * pderiv i P = 0) (t : K) :
    ∑ i, C ((A i).eval t) * pderiv i P = 0 := by
  let Q := ∑ i, C ((A i).eval t) * pderiv i P
  have hdvd : P - C t ∣ -Q := by
    have he : ∑ i, (Polynomial.aeval P (A i) - C ((A i).eval t)) * pderiv i P = -Q := by
      simp only [sub_mul, Finset.sum_sub_distrib, h, zero_sub, Q]
    rw [← he]
    apply Finset.dvd_sum
    intro i hi
    exact dvd_mul_of_dvd_left (polynomial_parameter_level_dvd_evaluation_difference P (A i) t) _
  have hQ : P - C t ∣ Q := dvd_neg.mp hdvd
  by_contra hne
  have hdeg : P.totalDegree ≤ (P - C t).totalDegree := by
    have he := totalDegree_add (P - C t) (C t)
    rwa [sub_add_cancel, totalDegree_C, max_zero] at he
  have hle := totalDegree_le_of_dvd_of_isDomain hQ hne
  have hlt : Q.totalDegree ≤ P.totalDegree - 1 := by
    apply totalDegree_finsetSum_le
    intro i _
    by_cases hi : pderiv i P = 0
    · simp [hi]
    · have hd := nonzero_polynomial_partial_totalDegree_succ_le P i hi
      apply (totalDegree_mul _ _).trans
      rw [totalDegree_C, zero_add]
      omega
  omega

end DimensionFourDependence
