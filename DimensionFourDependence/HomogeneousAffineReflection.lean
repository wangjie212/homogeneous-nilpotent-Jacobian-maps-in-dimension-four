import DimensionFourDependence.HomogeneousAffineLeadingCoefficient
import Mathlib.Algebra.Polynomial.Reverse

/-! # Homogeneous affine-line substitution reverses under interchange

Reflection at the prescribed homogeneous degree exchanges the base point
and direction, including when the substituted polynomial has smaller
actual degree. This identifies its next highest coefficient with a
first-order Taylor coefficient at the direction.
-/

namespace DimensionFourDependence

open MvPolynomial

variable {E ι : Type*} [CommRing E]

/-- Reflection is additive on finite sums at one fixed degree. -/
theorem polynomial_reflect_finset_sum (s : Finset ι) (f : ι → Polynomial E) (D : ℕ) :
    Polynomial.reflect D (∑ i ∈ s, f i) = ∑ i ∈ s, Polynomial.reflect D (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => simp only [Finset.sum_insert hi, Polynomial.reflect_add, ih]

/-- Reflection at the sum of prescribed degree bounds multiplies. -/
theorem polynomial_reflect_finset_product
    (s : Finset ι) (f : ι → Polynomial E) (d : ι → ℕ)
    (hf : ∀ i ∈ s, (f i).natDegree ≤ d i) :
    Polynomial.reflect (∑ i ∈ s, d i) (∏ i ∈ s, f i) =
      ∏ i ∈ s, Polynomial.reflect (d i) (f i) := by
  classical
  revert hf
  induction s using Finset.induction_on with
  | empty => intro _; simp
  | insert i s hi ih =>
    intro hf
    have hs : ∀ j ∈ s, (f j).natDegree ≤ d j := fun j hj => hf j (Finset.mem_insert_of_mem hj)
    have hp : (∏ j ∈ s, f j).natDegree ≤ ∑ j ∈ s, d j :=
      (Polynomial.natDegree_prod_le s f).trans (Finset.sum_le_sum hs)
    rw [Finset.sum_insert hi, Finset.prod_insert hi,
      Polynomial.reflect_mul _ _ (hf i (Finset.mem_insert_self i s)) hp,
      ih hs, Finset.prod_insert hi]

/-- Powers retain prescribed reflection bounds even after cancellation. -/
theorem polynomial_reflect_power (f : Polynomial E) {D : ℕ}
    (hf : f.natDegree ≤ D) (m : ℕ) :
    Polynomial.reflect (m * D) (f ^ m) = (Polynomial.reflect D f) ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ, Nat.succ_mul,
      Polynomial.reflect_mul _ _ (Polynomial.natDegree_pow_le_of_le m hf) hf, ih, pow_succ]

variable {K σ : Type*} [Field K] [Algebra K E]

/-- Reflection at the original homogeneous degree exchanges the
base point and direction of the entire substituted polynomial. -/
theorem homogeneous_affine_line_reflection
    (P : MvPolynomial σ K) {D : ℕ} (hP : P.IsHomogeneous D) (x A : σ → E) :
    Polynomial.reflect D
      (aeval (fun i => Polynomial.C (x i) + Polynomial.C (A i) * Polynomial.X) P) =
      aeval (fun i => Polynomial.C (A i) + Polynomial.C (x i) * Polynomial.X) P := by
  classical
  let f : σ → Polynomial E := fun i => Polynomial.C (x i) + Polynomial.C (A i) * Polynomial.X
  let g : σ → Polynomial E := fun i => Polynomial.C (A i) + Polynomial.C (x i) * Polynomial.X
  have hf (i : σ) : (f i).natDegree ≤ 1 := by
    apply Polynomial.natDegree_add_le_of_degree_le (by simp)
    exact Polynomial.natDegree_mul_le.trans (by simpa using (Polynomial.natDegree_X_le (R := E)))
  have hflip (i : σ) : Polynomial.reflect 1 (f i) = g i := by
    simp [f, g, Polynomial.reflect_add, Polynomial.reflect_C_mul, add_comm]
  change Polynomial.reflect D (aeval f P) = aeval g P
  conv_lhs => rw [P.as_sum, map_sum]
  conv_rhs => rw [P.as_sum, map_sum]
  rw [polynomial_reflect_finset_sum]
  apply Finset.sum_congr rfl
  intro d hd
  rw [aeval_monomial, aeval_monomial, Polynomial.algebraMap_apply,
    Polynomial.reflect_C_mul, hP.degree_eq_sum_deg_support hd]
  congr 1
  change Polynomial.reflect (∑ i ∈ d.support, d i) (∏ i ∈ d.support, f i ^ d i) =
    ∏ i ∈ d.support, g i ^ d i
  rw [polynomial_reflect_finset_product d.support (fun i => f i ^ d i) d
    (fun i _ => by simpa only [mul_one] using Polynomial.natDegree_pow_le_of_le (d i) (hf i))]
  apply Finset.prod_congr rfl
  intro i _
  simpa only [mul_one, hflip] using polynomial_reflect_power (f i) (hf i) (d i)

end DimensionFourDependence
