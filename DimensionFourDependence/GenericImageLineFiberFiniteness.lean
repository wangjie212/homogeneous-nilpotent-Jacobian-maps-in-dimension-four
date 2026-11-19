import DimensionFourDependence.ScalarExtendedImageEquation
import DimensionFourDependence.FiniteLineChartFibers
import DimensionFourDependence.GenericFiberOutput
import DimensionFourDependence.LineChartBaseChange

/-! # Finite line-parameter fibers over the actual generic image point

The actual evaluated normal is nonzero at the generic image value in
every extension of its function field. The actual image equation remains
irreducible there, so the smooth-point line-finiteness theorem applies.
The result also uses the coefficient equations over the original field,
as needed for the original-field covering components.
-/

namespace DimensionFourDependence

open MvPolynomial Matrix Module

variable {K E : Type*} [Field K] [Field E] [Algebra K E]
variable (H : Fin 4 → MvPolynomial (Fin 4) K)

/-- The finite original-field chart fiber depends only on the exact actual
image relations of the point. It therefore applies also to the universal
incidence's generic point, without choosing an isomorphic output field. -/
theorem ImageRelationWitness.finite_original_chart_fiber_of_relations [CharZero K]
    {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d)
    (hrank : polyRank (jac H) = 3) (hind : ¬ ComponentsDependent H)
    (I : ImageRelationWitness H) (O : Fin 4 → E)
    (hrel : ∀ P : MvPolynomial (Fin 4) K, aeval O P = 0 ↔ aeval H P = 0)
    (p : Equiv.Perm (Fin 4)) :
    {B : Matrix (Fin 2) (Fin 2) E |
      (∀ P ∈ graphLineEquationPolynomials (rename p.symm I.equation),
        extendedLineChartSpecialization B P = 0) ∧ O ∈ lineChartMemberLine p B}.Finite := by
  let : CharZero E := charZero_of_injective_algebraMap (algebraMap K E).injective
  have hdeg : 2 ≤ I.degree := by
    have hp := I.degree_pos
    by_contra hn
    have he : I.degree = 1 := by omega
    exact hind (I.dependent_of_degree_one H hd hH he)
  have hO : O ≠ 0 := by
    intro hz
    apply rank_three_polynomial_map_ne_zero H hrank
    funext i
    have hi := (hrel (X i)).mp (by rw [hz]; simp)
    simpa only [aeval_X, Pi.zero_apply] using hi
  have hzero : aeval (R := E) O (MvPolynomial.map (algebraMap K E) I.equation) = 0 := by
    rw [aeval_map_algebra_extension]
    exact (hrel I.equation).mpr I.vanishing
  have hsmooth : (fun i => aeval (R := E) O
      (pderiv i (MvPolynomial.map (algebraMap K E) I.equation))) ≠ 0 := by
    intro hz
    apply I.normal_ne_zero
    funext i
    have hi := congrFun hz i
    rw [MvPolynomial.pderiv_map, aeval_map_algebra_extension] at hi
    exact (hrel (pderiv i I.equation)).mp hi
  have hf := irreducible_hypersurface_finite_line_chart_fiber
    (MvPolynomial.map (algebraMap K E) I.equation) hdeg
    (I.homogeneous.map (algebraMap K E))
    (I.scalar_extended_equation_irreducible H hrank) O hO hzero hsmooth p
  apply hf.subset
  intro B hB
  refine ⟨?_, hB.2⟩
  have hb := (extended_line_chart_equations_iff B (rename p.symm I.equation)).mp hB.1
  simpa only [MvPolynomial.map_rename] using hb

variable [Algebra (polynomialOutputField H) E]
variable [IsScalarTower K (polynomialOutputField H) E]

/-- The actual generic image value satisfies the scalar-extended image equation. -/
theorem ImageRelationWitness.genericOutputValue_equation_zero
    (I : ImageRelationWitness H) :
    aeval (R := E) (genericOutputValue H E)
      (MvPolynomial.map (algebraMap K E) I.equation) = 0 := by
  rw [aeval_map_algebra_extension]
  exact (genericOutputValue_relations H E I.equation).mpr I.vanishing

/-- The original evaluated normal remains nonzero at the actual generic image value. -/
theorem ImageRelationWitness.genericOutputValue_gradient_ne_zero
    (I : ImageRelationWitness H) :
    (fun i => aeval (genericOutputValue H E) (pderiv i I.equation)) ≠ 0 := by
  intro hz
  apply I.normal_ne_zero
  funext i
  exact (genericOutputValue_relations H E (pderiv i I.equation)).mp
    (by simpa only [Pi.zero_apply] using congrFun hz i)

/-- The scalar-extended actual equation is smooth at the actual generic image value. -/
theorem ImageRelationWitness.genericOutputValue_scalar_extended_smooth
    (I : ImageRelationWitness H) :
    (fun i => aeval (R := E) (genericOutputValue H E)
      (pderiv i (MvPolynomial.map (algebraMap K E) I.equation))) ≠ 0 := by
  intro hz
  apply I.genericOutputValue_gradient_ne_zero (E := E) H
  funext i
  have hi := congrFun hz i
  rw [MvPolynomial.pderiv_map, aeval_map_algebra_extension] at hi
  exact hi

variable [CharZero K]

/-- There are finitely many actual image lines through the geometric generic
image point, in every extension of the actual image function field. -/
theorem ImageRelationWitness.genericOutputValue_finite_lines
    {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d)
    (hrank : polyRank (jac H) = 3) (hind : ¬ ComponentsDependent H)
    (I : ImageRelationWitness H) :
    {L : Submodule E (Fin 4 → E) | finrank E L = 2 ∧ genericOutputValue H E ∈ L ∧
      (∀ x ∈ L, aeval x (MvPolynomial.map (algebraMap K E) I.equation) = 0)}.Finite := by
  let : CharZero E := charZero_of_injective_algebraMap (algebraMap K E).injective
  have hdeg : 2 ≤ I.degree := by
    have hp := I.degree_pos
    by_contra hn
    have he : I.degree = 1 := by omega
    exact hind (I.dependent_of_degree_one H hd hH he)
  exact irreducible_hypersurface_finite_lines_at_smooth_point
    (MvPolynomial.map (algebraMap K E) I.equation) hdeg
    (I.homogeneous.map (algebraMap K E))
    (I.scalar_extended_equation_irreducible H hrank) (genericOutputValue H E)
    (genericOutputValue_ne_zero H (rank_three_polynomial_map_ne_zero H hrank) E)
    (I.genericOutputValue_equation_zero H) (I.genericOutputValue_scalar_extended_smooth H)

/-- Every actual matrix chart has a finite parameter fiber over the geometric
generic image point. -/
theorem ImageRelationWitness.genericOutputValue_finite_line_chart_fiber
    {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d)
    (hrank : polyRank (jac H) = 3) (hind : ¬ ComponentsDependent H)
    (I : ImageRelationWitness H) (p : Equiv.Perm (Fin 4)) :
    {B : Matrix (Fin 2) (Fin 2) E |
      B ∈ hypersurfaceLineChart (rename p.symm (MvPolynomial.map (algebraMap K E) I.equation)) ∧
      genericOutputValue H E ∈ lineChartMemberLine p B}.Finite := by
  exact finite_line_chart_fiber_of_finite_contained_lines _ _
    (I.genericOutputValue_finite_lines H hd hH hrank hind) p

/-- The same fiber is finite when its equations are written over the original
coefficient field, as in the original-field minimal-prime covering component. -/
theorem ImageRelationWitness.genericOutputValue_finite_original_chart_fiber
    {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d)
    (hrank : polyRank (jac H) = 3) (hind : ¬ ComponentsDependent H)
    (I : ImageRelationWitness H) (p : Equiv.Perm (Fin 4)) :
    {B : Matrix (Fin 2) (Fin 2) E |
      (∀ P ∈ graphLineEquationPolynomials (rename p.symm I.equation),
        extendedLineChartSpecialization B P = 0) ∧
      genericOutputValue H E ∈ lineChartMemberLine p B}.Finite := by
  apply (I.genericOutputValue_finite_line_chart_fiber H hd hH hrank hind p).subset
  intro B hB
  refine ⟨?_, hB.2⟩
  have hb := (extended_line_chart_equations_iff B (rename p.symm I.equation)).mp hB.1
  simpa only [MvPolynomial.map_rename] using hb

end DimensionFourDependence
