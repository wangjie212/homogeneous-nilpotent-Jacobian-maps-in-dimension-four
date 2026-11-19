import DimensionFourDependence.GraphHilbert

/-! # Selecting affine coordinates cannot increase the actual Hilbert function

The chart evaluation range of selected coordinates is a subspace of the
original evaluation range in every degree. The dimensions are the actual
homogeneous quotient dimensions of their entire projective closure ideals.
-/

namespace DimensionFourDependence

open MvPolynomial Module

variable {L F sigma tau : Type*} [Field L] [Field F] [Algebra L F]

/-- A coordinate selection on the actual homogeneous polynomial spaces. -/
noncomputable def homogeneousCoordinateSelection (f : tau → sigma) (d : ℕ) :
    homogeneousSubmodule (Option tau) L d →ₗ[L] homogeneousSubmodule (Option sigma) L d where
  toFun P := ⟨rename (Option.map f) (P : MvPolynomial (Option tau) L), P.property.rename_isHomogeneous⟩
  map_add' P Q := Subtype.ext ((rename (R := L) (Option.map f)).map_add
    (P : MvPolynomial (Option tau) L) (Q : MvPolynomial (Option tau) L))
  map_smul' a P := Subtype.ext ((rename (R := L) (Option.map f)).toLinearMap.map_smul
    a (P : MvPolynomial (Option tau) L))

/-- Actual chart evaluation of selected coordinates factors through
their original homogeneous-coordinate inclusion. -/
theorem homogeneousChartEvaluation_coordinate_selection (x : sigma → F) (f : tau → sigma) (d : ℕ) :
    homogeneousChartEvaluation (L := L) (x ∘ f) d =
      (homogeneousChartEvaluation (L := L) x d).comp (homogeneousCoordinateSelection f d) := by
  apply LinearMap.ext
  intro P
  change aeval (fun j : Option tau => j.elim 1 (x ∘ f)) (P : MvPolynomial (Option tau) L) =
    aeval (fun j : Option sigma => j.elim 1 x) (rename (Option.map f) (P : MvPolynomial (Option tau) L))
  rw [aeval_rename]
  have he : (fun j : Option tau => j.elim 1 (x ∘ f)) =
      (fun j : Option sigma => j.elim 1 x) ∘ Option.map f := by
    funext j
    cases j <;> rfl
  rw [he]

/-- Every coordinate projection has no larger actual projective
Hilbert function, even if the selected labels repeat. -/
theorem projectiveHilbertFunction_coordinate_projection_le [Finite sigma]
    (x : sigma → F) (f : tau → sigma) (d : ℕ) :
    projectiveHilbertFunction (projectiveConeIdeal (L := L) (x ∘ f)) d ≤
      projectiveHilbertFunction (projectiveConeIdeal (L := L) x) d := by
  rw [projectiveHilbertFunction_cone_eq_chart_rank, projectiveHilbertFunction_cone_eq_chart_rank,
    homogeneousChartEvaluation_coordinate_selection]
  exact Submodule.finrank_mono (LinearMap.range_comp_le_range _ _)

end DimensionFourDependence
