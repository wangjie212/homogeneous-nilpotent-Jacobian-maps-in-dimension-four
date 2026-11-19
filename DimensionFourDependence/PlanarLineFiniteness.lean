import DimensionFourDependence.PlanarLineCoordinates
import DimensionFourDependence.HomogeneousEvaluationScaling

/-! # Finitely many contained plane lines through a fixed point

A nonzero homogeneous plane equation is nonzero somewhere on the chart
with second coordinate one. Fixing the first coordinate there gives a
nonzero univariate polynomial. Every admissible line slope is its root;
the single exceptional line completes the finiteness argument.
-/

namespace DimensionFourDependence

open MvPolynomial Module

variable {F : Type*} [Field F] [Infinite F]

/-- A nonzero homogeneous plane form is nonzero somewhere on the
second-coordinate affine chart. -/
theorem homogeneous_plane_exists_normalized_nonzero
    (R : MvPolynomial (Fin 3) F) {d : ℕ} (hR : R.IsHomogeneous d) (hR0 : R ≠ 0) :
    ∃ s t : F, aeval (![s, 1, t] : Fin 3 → F) R ≠ 0 := by
  classical
  by_contra hnone
  push Not at hnone
  have hinf : Set.Infinite {a : F | a ≠ 0} := by
    convert Set.infinite_univ.sdiff (Set.finite_singleton (0 : F)) using 1
    ext a
    simp
  apply hR0
  apply MvPolynomial.funext_set (fun i : Fin 3 => if i = 1 then {a : F | a ≠ 0} else Set.univ)
  · intro i
    split_ifs
    · exact hinf
    · exact Set.infinite_univ
  · intro x hx
    have hx1 : x 1 ≠ 0 := by simpa using hx (1 : Fin 3) (Set.mem_univ _)
    change aeval x R = aeval x (0 : MvPolynomial (Fin 3) F)
    rw [map_zero]
    have hpoint : x = fun i => x 1 * (![x 0 / x 1, 1, x 2 / x 1] : Fin 3 → F) i := by
      funext i
      fin_cases i <;> dsimp <;> field_simp
    rw [hpoint, homogeneous_aeval_scale R hR, hnone, mul_zero]

/-- A univariate slice of the normalized plane equation. -/
noncomputable def planarLineSlopePolynomial (R : MvPolynomial (Fin 3) F) (s : F) : Polynomial F :=
  aeval (![Polynomial.C s, 1, Polynomial.X] : Fin 3 → Polynomial F) R

omit [Infinite F] in
/-- Evaluation of the slope polynomial is evaluation at the normalized plane point. -/
theorem planarLineSlopePolynomial_eval (R : MvPolynomial (Fin 3) F) (s t : F) :
    Polynomial.aeval t (planarLineSlopePolynomial R s) = aeval (![s, 1, t] : Fin 3 → F) R := by
  have he := comp_aeval_apply (![Polynomial.C s, 1, Polynomial.X] : Fin 3 → Polynomial F)
    (Polynomial.aeval t) R
  have hp : (fun i => Polynomial.aeval t ((![Polynomial.C s, 1, Polynomial.X] : Fin 3 → Polynomial F) i)) =
      (![s, 1, t] : Fin 3 → F) := by
    funext i
    fin_cases i <;> simp
  rw [hp] at he
  exact he

/-- The finite slopes of lines contained in a nonzero homogeneous plane equation form a finite set. -/
theorem homogeneous_plane_finite_contained_slopes
    (R : MvPolynomial (Fin 3) F) {d : ℕ} (hR : R.IsHomogeneous d) (hR0 : R ≠ 0) :
    {m : F | ∀ x ∈ standardPlaneLine m, aeval x R = 0}.Finite := by
  obtain ⟨s, t, hst⟩ := homogeneous_plane_exists_normalized_nonzero R hR hR0
  have hp : planarLineSlopePolynomial R s ≠ 0 := by
    intro hz
    have he := planarLineSlopePolynomial_eval R s t
    rw [hz, map_zero] at he
    exact hst he.symm
  apply (Polynomial.finite_setOfPred_isRoot hp).subset
  intro m hm
  change Polynomial.aeval m (planarLineSlopePolynomial R s) = 0
  rw [planarLineSlopePolynomial_eval]
  exact hm _ (standardPlaneLine_normalized_point_mem m s)

/-- Only finitely many projective lines through the first coordinate
point can lie on a nonzero homogeneous plane equation. -/
theorem homogeneous_plane_finite_lines_through_first_point
    (R : MvPolynomial (Fin 3) F) {d : ℕ} (hR : R.IsHomogeneous d) (hR0 : R ≠ 0) :
    {L : Submodule F (Fin 3 → F) | finrank F L = 2 ∧
      (![1, 0, 0] : Fin 3 → F) ∈ L ∧ (∀ x ∈ L, aeval x R = 0)}.Finite := by
  have hs := homogeneous_plane_finite_contained_slopes R hR hR0
  apply ((Set.finite_singleton (standardVerticalPlaneLine (F := F))).union
    (hs.image (standardPlaneLine (F := F)))).subset
  intro L hL
  rcases plane_line_through_first_point_classification L hL.1 hL.2.1 with he | ⟨m, he⟩
  · exact Or.inl he
  · refine Or.inr ⟨m, ?_, he.symm⟩
    change ∀ x ∈ standardPlaneLine m, aeval x R = 0
    simpa only [he] using hL.2.2

end DimensionFourDependence
