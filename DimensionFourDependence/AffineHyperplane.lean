import DimensionFourDependence.FiberEquationSystem

/-! # Solving the verified affine hyperplane equation

This provides the elimination step needed to identify the projected fiber's
function field with the original source function field.
-/

namespace DimensionFourDependence

open MvPolynomial

variable {R σ : Type*} [Field R]

/-- Subtracting the constant term of an affine-linear polynomial leaves
a homogeneous linear polynomial. -/
theorem affine_sub_constant_isHomogeneous (p : MvPolynomial σ R) (hp : p.totalDegree ≤ 1) :
    (p - C (p.coeff 0)).IsHomogeneous 1 := by
  classical
  intro m hm
  change (Finsupp.weight (fun _ : σ => (1 : ℕ))) m = 1
  rw [← Finsupp.degree_eq_weight_one]
  have hm0 : m ≠ 0 := by
    intro h
    subst m
    simp at hm
  have hc : p.coeff m ≠ 0 := by simpa [hm0, Ne.symm hm0] using hm
  have hle : m.degree ≤ 1 := by
    simpa only [Finsupp.degree_apply, Finsupp.sum] using
      (le_totalDegree (mem_support_iff.mpr hc)).trans hp
  have hne : m.degree ≠ 0 := fun h => hm0 ((Finsupp.degree_eq_zero_iff m).mp h)
  omega

/-- Every partial derivative of an affine-linear polynomial is its
constant coefficient. -/
theorem affine_pderiv_eq_C (p : MvPolynomial σ R) (hp : p.totalDegree ≤ 1) (i : σ) :
    pderiv i p = C ((pderiv i p).coeff 0) := by
  have hh := (affine_sub_constant_isHomogeneous p hp).pderiv (i := i)
  simp only [map_sub, pderiv_C, sub_zero, Nat.reduceSub] at hh
  exact eq_C_of_isHomogeneous_zero hh

/-- The explicit linear expansion of an affine-linear polynomial. -/
theorem affine_polynomial_expansion [Fintype σ] (p : MvPolynomial σ R) (hp : p.totalDegree ≤ 1) :
    p = C (p.coeff 0) + ∑ i, C ((pderiv i p).coeff 0) * X i := by
  have he := (affine_sub_constant_isHomogeneous p hp).sum_X_mul_pderiv
  simp only [one_smul, map_sub, pderiv_C, sub_zero] at he
  have hs : (∑ i, X i * pderiv i p) =
      ∑ i, C ((pderiv i p).coeff 0) * X i := by
    apply Finset.sum_congr rfl
    intro i _
    calc
      X i * pderiv i p = X i * C ((pderiv i p).coeff 0) :=
        congrArg (fun z => X i * z) (affine_pderiv_eq_C p hp i)
      _ = C ((pderiv i p).coeff 0) * X i := mul_comm _ _
  rw [hs] at he
  linear_combination -he

variable {A : Type*} [Field A] [Algebra R A] {n : ℕ}

/-- A unit last derivative solves the affine equation for its last
coordinate over any extension field. -/
theorem affine_hyperplane_solve_last (p : MvPolynomial (Fin (n + 1)) R)
    (hp : p.totalDegree ≤ 1) (hlast : pderiv (Fin.last n) p = 1)
    (x : Fin (n + 1) → A) (hzero : aeval x p = 0) :
    x (Fin.last n) = -algebraMap R A (p.coeff 0) - ∑ i : Fin n,
      algebraMap R A ((pderiv i.castSucc p).coeff 0) * x i.castSucc := by
  have he := congrArg (aeval x) (affine_polynomial_expansion p hp)
  simp only [map_add, map_sum, map_mul, aeval_C, aeval_X, hzero] at he
  rw [Fin.sum_univ_castSucc, hlast] at he
  simp only [coeff_one, ite_true, map_one, one_mul] at he
  linear_combination -he

/-- Consequently, the last coordinate belongs to the field generated
by the first coordinates over the coefficient field. -/
theorem affine_hyperplane_last_mem_adjoin (p : MvPolynomial (Fin (n + 1)) R)
    (hp : p.totalDegree ≤ 1) (hlast : pderiv (Fin.last n) p = 1)
    (x : Fin (n + 1) → A) (hzero : aeval x p = 0) :
    x (Fin.last n) ∈ IntermediateField.adjoin R (Set.range (fun i : Fin n => x i.castSucc)) := by
  rw [affine_hyperplane_solve_last p hp hlast x hzero]
  apply IntermediateField.sub_mem
  · exact IntermediateField.neg_mem _ (IntermediateField.algebraMap_mem _ _)
  · apply IntermediateField.sum_mem
    intro i _
    apply IntermediateField.mul_mem
    · exact IntermediateField.algebraMap_mem _ _
    · exact IntermediateField.subset_adjoin R _ ⟨i, rfl⟩

end DimensionFourDependence
