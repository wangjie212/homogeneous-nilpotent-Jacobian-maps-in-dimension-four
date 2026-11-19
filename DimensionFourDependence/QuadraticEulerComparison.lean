import DimensionFourDependence.AffineConeTrace

/-! # Quadratic components of the transverse Euler expression

These coefficient-ring statements keep K[t] as constants while taking
homogeneous components in the actual two transverse variables.
-/

namespace DimensionFourDependence

open MvPolynomial

set_option maxHeartbeats 3000000

variable {R S : Type*} [CommRing R] [CommRing S] {n : ℕ}

/-- The Euler coefficient formula over an arbitrary coefficient ring,
including the polynomial parameter ring. -/
theorem coefficient_ring_euler_coefficient
    (p : MvPolynomial (Fin n) R) (m : Fin n →₀ ℕ) :
    (∑ i : Fin n, X i * pderiv i p).coeff m = (m.degree : R) * p.coeff m := by
  classical
  induction p using MvPolynomial.induction_on' with
  | add p q hp hq =>
    simp only [map_add, mul_add, Finset.sum_add_distrib, AddMonoidAlgebra.coeff_add,
      Finsupp.add_apply] at *
    rw [hp, hq]
  | monomial s a =>
    have h := (isHomogeneous_monomial a (n := s.degree) rfl).sum_X_mul_pderiv
    rw [h, coeff_smul]
    by_cases hm : s = m
    · subst s; simp [nsmul_eq_mul]
    · simp [coeff_monomial, hm]

/-- The quadratic homogeneous component of Euler(Q)-Q is exactly Q₂. -/
theorem quadratic_component_euler_sub_self
    (Q : MvPolynomial (Fin n) R) :
    homogeneousComponent 2 ((∑ i : Fin n, X i * pderiv i Q) - Q) = homogeneousComponent 2 Q := by
  classical
  ext m
  simp only [coeff_homogeneousComponent, coeff_sub, coefficient_ring_euler_coefficient]
  by_cases hm : m.degree = 2
  · change (if m.degree = 2 then (m.degree : R) * Q.coeff m - Q.coeff m else 0) =
      (if m.degree = 2 then Q.coeff m else 0)
    rw [hm]
    norm_num
    ring
  · change (if m.degree = 2 then (m.degree : R) * Q.coeff m - Q.coeff m else 0) =
      (if m.degree = 2 then Q.coeff m else 0)
    simp only [hm, ite_false]

/-- Partial differentiation of a degree-at-most-two polynomial has
transverse degree at most one, over the full original coefficient ring. -/
theorem quadratic_polynomial_partial_degree_le_one
    (Q : MvPolynomial (Fin n) R) (hQ : Q.totalDegree ≤ 2) (i : Fin n) :
    (pderiv i Q).totalDegree ≤ 1 := by
  classical
  apply Finset.sup_le
  intro m hm
  have hcoeff : Q.coeff (m + Finsupp.single i 1) ≠ 0 := by
    intro hz
    have he := mem_support_iff.mp hm
    rw [coeff_pderiv, hz, zero_mul] at he
    exact he rfl
  have he := (le_totalDegree (mem_support_iff.mpr hcoeff)).trans hQ
  change (m + Finsupp.single i 1).degree ≤ 2 at he
  have hdeg : (m + Finsupp.single i 1).degree = m.degree + 1 := by
    simp only [map_add, Finsupp.degree_single]
  rw [hdeg] at he
  change m.degree ≤ 1
  omega

/-- Coefficient extension commutes with each homogeneous component in
the transverse variables. -/
theorem homogeneous_component_coefficient_map
    (f : R →+* S) (Q : MvPolynomial (Fin n) R) (d : ℕ) :
    homogeneousComponent d (MvPolynomial.map f Q) = MvPolynomial.map f (homogeneousComponent d Q) := by
  classical
  ext m
  simp only [coeff_homogeneousComponent, coeff_map]
  split_ifs <;> simp only [map_zero]

end DimensionFourDependence
