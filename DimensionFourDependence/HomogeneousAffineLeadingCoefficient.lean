import DimensionFourDependence.MonicHypersurfaceProjection
import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-! # Highest coefficients of homogeneous forms on affine lines

The coefficient at the specified degree of a product is the product of
the corresponding highest allowed coefficients, even when some factors
have smaller degree. Applying this to each original monomial shows that
the highest coefficient of a homogeneous form on an affine line is its
value at the direction vector.
-/

namespace DimensionFourDependence

open MvPolynomial

variable {E iota : Type*} [CommRing E]

/-- Highest allowed coefficients multiply for arbitrary individual
degree bounds, including zero factors and smaller actual degrees. -/
theorem polynomial_product_coefficient_at_sum_bound
    (s : Finset iota) (f : iota → Polynomial E) (d : iota → ℕ)
    (hf : ∀ i ∈ s, (f i).natDegree ≤ d i) :
    (∏ i ∈ s, f i).coeff (∑ i ∈ s, d i) = ∏ i ∈ s, (f i).coeff (d i) := by
  classical
  revert hf
  induction s using Finset.induction_on with
  | empty => intro _; simp
  | @insert i s hi ih =>
    intro hf
    have hs : ∀ j ∈ s, (f j).natDegree ≤ d j := fun j hj => hf j (Finset.mem_insert_of_mem hj)
    have hprod : (∏ j ∈ s, f j).natDegree ≤ ∑ j ∈ s, d j :=
      (Polynomial.natDegree_prod_le s f).trans (Finset.sum_le_sum hs)
    rw [Finset.prod_insert hi, Finset.sum_insert hi, Finset.prod_insert hi,
      Polynomial.coeff_mul_add_eq_of_natDegree_le (hf i (Finset.mem_insert_self i s)) hprod, ih hs]

variable {K sigma : Type*} [Field K] [Algebra K E]

/-- Substituting polynomials of degree at most one in an original
homogeneous form gives the direction-value as its top allowed coefficient. -/
theorem homogeneous_aeval_coefficient_at_degree
    (P : MvPolynomial sigma K) {D : ℕ} (hP : P.IsHomogeneous D)
    (s : sigma → Polynomial E) (hs : ∀ i, (s i).natDegree ≤ 1) :
    (aeval s P).coeff D = aeval (fun i => (s i).coeff 1) P := by
  classical
  conv_lhs => rw [P.as_sum, map_sum]
  conv_rhs => rw [P.as_sum, map_sum]
  rw [Polynomial.finsetSum_coeff]
  apply Finset.sum_congr rfl
  intro d hd
  rw [aeval_monomial, aeval_monomial, Polynomial.algebraMap_apply, Polynomial.coeff_C_mul]
  rw [hP.degree_eq_sum_deg_support hd]
  congr 1
  change (∏ i ∈ d.support, s i ^ d i).coeff (∑ i ∈ d.support, d i) =
    ∏ i ∈ d.support, ((s i).coeff 1) ^ d i
  rw [polynomial_product_coefficient_at_sum_bound d.support (fun i => s i ^ d i) d
    (fun i _ => by simpa only [mul_one] using Polynomial.natDegree_pow_le_of_le (d i) (hs i))]
  apply Finset.prod_congr rfl
  intro i _
  simpa only [mul_one] using Polynomial.coeff_pow_of_natDegree_le (m := d i) (hs i)

/-- The highest original homogeneous coefficient on the actual
affine line is evaluation at its specified direction vector. -/
theorem homogeneous_affine_line_coefficient_at_degree
    (P : MvPolynomial sigma K) {D : ℕ} (hP : P.IsHomogeneous D)
    (x A : sigma → E) :
    (aeval (fun i => Polynomial.C (x i) + Polynomial.C (A i) * Polynomial.X) P).coeff D =
      aeval A P := by
  have hs (i : sigma) :
      (Polynomial.C (x i) + Polynomial.C (A i) * Polynomial.X).natDegree ≤ 1 := by
    apply Polynomial.natDegree_add_le_of_degree_le (by simp)
    exact Polynomial.natDegree_mul_le.trans (by simpa using (Polynomial.natDegree_X_le (R := E)))
  simpa using homogeneous_aeval_coefficient_at_degree P hP _ hs

end DimensionFourDependence
