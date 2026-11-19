import DimensionFourDependence.AffineTriangularFlow
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors

/-! # Tangency along an affine level gives global annihilation

An affine triangular tangent action does not increase polynomial degree.
If a nonzero polynomial divides its tangent derivative, the quotient is
constant. The explicit polynomial-flow eigenvalue obstruction then makes
that derivative zero. This is the global-annihilation step after (4.10).
-/

namespace DimensionFourDependence

open MvPolynomial

set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 100000

variable {K : Type*} [Field K]

/-- A nonzero actual partial derivative lowers the original polynomial's
total degree by at least one. -/
theorem nonzero_polynomial_partial_totalDegree_succ_le
    {n : ℕ} (P : MvPolynomial (Fin n) K) (i : Fin n) (hi : pderiv i P ≠ 0) :
    (pderiv i P).totalDegree + 1 ≤ P.totalDegree := by
  classical
  obtain ⟨m, hm, hmax⟩ := (pderiv i P).support.exists_mem_eq_sup
    (support_nonempty.mpr hi) (fun m => m.sum fun _ e => e)
  have hm' : m + Finsupp.single i 1 ∈ P.support := by
    rw [mem_support_iff] at hm ⊢
    rw [coeff_pderiv] at hm
    exact (mul_ne_zero_iff.mp hm).1
  have hs : (m + Finsupp.single i 1).sum (fun _ e => e) = m.sum (fun _ e => e) + 1 := by
    simp [Finsupp.sum_add_index']
  have h := le_totalDegree hm'
  rw [hs] at h
  simpa only [totalDegree, hmax] using h

/-- Each original constant horizontal coefficient and affine vertical
coefficient has degree at most one. -/
theorem affineTangentVerticalCoefficient_totalDegree_le_one (b : Fin 3 → K) :
    (affineTangentVerticalCoefficient b).totalDegree ≤ 1 := by
  apply (totalDegree_add _ _).trans
  refine max_le ?_ ?_
  · apply (totalDegree_add _ _).trans
    exact max_le (by simp) ((totalDegree_mul _ _).trans (by simp))
  · exact (totalDegree_mul _ _).trans (by simp)

/-- The full actual affine triangular tangent action never increases
the original polynomial's total degree, including all zero-partial cases. -/
theorem affineProjectedTangentAction_totalDegree_le
    (u : Fin 2 → K) (b : Fin 3 → K) (P : MvPolynomial (Fin 3) K) :
    (affineProjectedTangentAction u b P).totalDegree ≤ P.totalDegree := by
  have hterm (i : Fin 3) (c : MvPolynomial (Fin 3) K) (hc : c.totalDegree ≤ 1) :
      (c * pderiv i P).totalDegree ≤ P.totalDegree := by
    by_cases hz : pderiv i P = 0
    · simp [hz]
    · have hd := nonzero_polynomial_partial_totalDegree_succ_le P i hz
      exact (totalDegree_mul _ _).trans (by omega)
  unfold affineProjectedTangentAction
  apply (totalDegree_add _ _).trans
  refine max_le ?_ (hterm 2 _ (affineTangentVerticalCoefficient_totalDegree_le_one b))
  apply (totalDegree_add _ _).trans
  exact max_le (hterm 0 _ (by simp)) (hterm 1 _ (by simp))

variable [CharZero K]

/-- Divisibility by a nonzero polynomial turns the full affine triangular
tangent action into global annihilation. The scalar cofactor is derived
from degree, and its vanishing is derived from the explicit flow. -/
theorem affine_triangular_polynomial_dvd_action_iff_zero
    (u : Fin 2 → K) (b : Fin 3 → K) (P : MvPolynomial (Fin 3) K) (hP : P ≠ 0) :
    P ∣ affineProjectedTangentAction u b P ↔ affineProjectedTangentAction u b P = 0 := by
  constructor
  · intro hdvd
    by_cases hz : affineProjectedTangentAction u b P = 0
    · exact hz
    obtain ⟨Q, hQ⟩ := hdvd
    have hQ0 : Q ≠ 0 := by
      intro hzero
      rw [hzero, mul_zero] at hQ
      exact hz hQ
    have hdegree := affineProjectedTangentAction_totalDegree_le u b P
    rw [hQ, totalDegree_mul_of_isDomain hP hQ0] at hdegree
    have hQdegree : Q.totalDegree = 0 := by omega
    have hQconstant := totalDegree_eq_zero_iff_eq_C.mp hQdegree
    have heigen : affineProjectedTangentAction u b P = C (Q.coeff 0) * P := by
      calc
        _ = P * Q := hQ
        _ = P * C (Q.coeff 0) := congrArg (fun q => P * q) hQconstant
        _ = _ := mul_comm _ _
    have hscalar := affine_triangular_polynomial_eigenvalue_zero u b P hP (Q.coeff 0) heigen
    rw [hscalar, map_zero, zero_mul] at heigen
    exact heigen
  · intro hz
    rw [hz]
    exact dvd_zero P

omit [CharZero K] in
/-- Subtracting the level scalar does not change the full affine
triangular tangent derivative. -/
theorem affineProjectedTangentAction_sub_C
    (u : Fin 2 → K) (b : Fin 3 → K) (P : MvPolynomial (Fin 3) K) (t : K) :
    affineProjectedTangentAction u b (P - C t) = affineProjectedTangentAction u b P := by
  simp [affineProjectedTangentAction]

/-- Tangency modulo the nonzero literal level equation P-t forces the
whole original polynomial P to be annihilated identically. -/
theorem affine_triangular_level_tangency_forces_global_annihilation
    (u : Fin 2 → K) (b : Fin 3 → K) (P : MvPolynomial (Fin 3) K) (t : K)
    (hlevel : P - C t ≠ 0) (htangent : P - C t ∣ affineProjectedTangentAction u b P) :
    affineProjectedTangentAction u b P = 0 := by
  have hdiv : P - C t ∣ affineProjectedTangentAction u b (P - C t) := by
    rw [affineProjectedTangentAction_sub_C]
    exact htangent
  have h := (affine_triangular_polynomial_dvd_action_iff_zero u b (P - C t) hlevel).mp hdiv
  rwa [affineProjectedTangentAction_sub_C] at h

end DimensionFourDependence
