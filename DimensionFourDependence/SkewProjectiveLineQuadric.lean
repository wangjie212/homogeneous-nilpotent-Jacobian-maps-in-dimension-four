import DimensionFourDependence.ThreeLineQuadricUniqueness

/-! # Quadric geometry for three skew lines in projective three-space

Projective lines are represented by two-dimensional vector subspaces.
Their skewness is disjointness of those subspaces. The four-dimensional
ambient-space hypothesis supplies the complementary-subspace conditions;
the coordinate normal form, transversal containment and uniqueness of
the quadratic form are then consequences, not extra geometric hypotheses.
-/

namespace DimensionFourDependence

variable {F A : Type*} [Field F] [AddCommGroup A] [Module F A]

/-- Disjoint two-dimensional subspaces of a four-dimensional space are complementary. -/
theorem skew_line_subspaces_isCompl [FiniteDimensional F A]
    (hA : Module.finrank F A = 4) (U V : Submodule F A)
    (hU : Module.finrank F U = 2) (hV : Module.finrank F V = 2) (hUV : Disjoint U V) :
    IsCompl U V := by
  exact (Submodule.isCompl_iff_disjoint U V (by rw [hA, hU, hV])).mpr hUV

/-- Quadratic forms through three lines in their standard coordinates
are uniquely determined up to a scalar. -/
theorem quadratic_form_three_line_coordinates_unique
    (U V W : Submodule F A) (e : A ≃ₗ[F] ((Fin 2 → F) × (Fin 2 → F)))
    (hU : ∀ x, (e x).2 = 0 ↔ x ∈ U) (hV : ∀ x, (e x).1 = 0 ↔ x ∈ V)
    (hW : ∀ x, (e x).1 = (e x).2 ↔ x ∈ W)
    (Q : QuadraticForm F A) (hQU : ∀ x ∈ U, Q x = 0)
    (hQV : ∀ x ∈ V, Q x = 0) (hQW : ∀ x ∈ W, Q x = 0) :
    ∃! d : F, Q = d • (standardRulingQuadraticForm.comp e.toLinearMap) := by
  let R := Q.comp e.symm.toLinearMap
  have hfirst (a : Fin 2 → F) : R (a, 0) = 0 := by
    apply hQU
    apply (hU _).mp
    simp
  have hsecond (a : Fin 2 → F) : R (0, a) = 0 := by
    apply hQV
    apply (hV _).mp
    simp
  have hdiag (a : Fin 2 → F) : R (a, a) = 0 := by
    apply hQW
    apply (hW _).mp
    simp
  obtain ⟨d, hd⟩ := quadratic_form_vanishing_on_three_standard_lines R hfirst hsecond hdiag
  have heq : Q = d • (standardRulingQuadraticForm.comp e.toLinearMap) := by
    ext x
    have hx := hd (e x)
    simpa [R, QuadraticMap.comp_apply, standardRulingQuadraticForm_apply] using hx
  refine ⟨d, heq, ?_⟩
  intro c hc
  let x := e.symm (![1, 0], ![0, 1])
  have hv := congrArg (fun T : QuadraticForm F A => T x) (hc.symm.trans heq)
  simpa [x, QuadraticMap.comp_apply, standardRulingQuadraticForm_apply,
    standardRulingQuadric] using hv

/-- Three skew projective lines have an axis/axis/diagonal coordinate normal form. -/
theorem three_skew_projective_lines_coordinate_normal_form [FiniteDimensional F A]
    (hA : Module.finrank F A = 4) (U V W : Submodule F A)
    (hU : Module.finrank F U = 2) (hV : Module.finrank F V = 2)
    (hW : Module.finrank F W = 2) (hUV : Disjoint U V) (hUW : Disjoint U W)
    (hVW : Disjoint V W) :
    ∃ e : A ≃ₗ[F] ((Fin 2 → F) × (Fin 2 → F)),
      (∀ x, (e x).2 = 0 ↔ x ∈ U) ∧
      (∀ x, (e x).1 = 0 ↔ x ∈ V) ∧
      (∀ x, (e x).1 = (e x).2 ↔ x ∈ W) := by
  exact three_skew_lines_coordinate_normal_form U V W
    (skew_line_subspaces_isCompl hA U V hU hV hUV)
    (skew_line_subspaces_isCompl hA U W hU hW hUW)
    (skew_line_subspaces_isCompl hA V W hV hW hVW) hW

/-- The elementary three-skew-lines quadric step in Section 3.2:
the quadric contains every common transversal, and every quadratic form
through the three lines is a unique scalar multiple of its equation.
Existence of the covering families and density of their incidence are separate questions. -/
theorem three_skew_projective_lines_quadric [FiniteDimensional F A]
    (hA : Module.finrank F A = 4) (U V W : Submodule F A)
    (hU : Module.finrank F U = 2) (hV : Module.finrank F V = 2)
    (hW : Module.finrank F W = 2) (hUV : Disjoint U V) (hUW : Disjoint U W)
    (hVW : Disjoint V W) :
    ∃ e : A ≃ₗ[F] ((Fin 2 → F) × (Fin 2 → F)),
      (∀ x ∈ U, standardRulingQuadric (e x) = 0) ∧
      (∀ x ∈ V, standardRulingQuadric (e x) = 0) ∧
      (∀ x ∈ W, standardRulingQuadric (e x) = 0) ∧
      (∀ (L : Submodule F A), Module.finrank F L = 2 →
        (∃ x : A, x ≠ 0 ∧ x ∈ L ∧ x ∈ U) →
        (∃ x : A, x ≠ 0 ∧ x ∈ L ∧ x ∈ V) →
        (∃ x : A, x ≠ 0 ∧ x ∈ L ∧ x ∈ W) →
        ∀ x ∈ L, standardRulingQuadric (e x) = 0) ∧
      (∀ (Q : QuadraticForm F A), (∀ x ∈ U, Q x = 0) →
        (∀ x ∈ V, Q x = 0) → (∀ x ∈ W, Q x = 0) →
        ∃! d : F, Q = d • (standardRulingQuadraticForm.comp e.toLinearMap)) := by
  obtain ⟨e, heU, heV, heW⟩ := three_skew_projective_lines_coordinate_normal_form
    hA U V W hU hV hW hUV hUW hVW
  refine ⟨e, ?_, ?_, ?_,
    coordinate_quadric_contains_transversal U V W e heU heV heW,
    quadratic_form_three_line_coordinates_unique U V W e heU heV heW⟩
  · intro x hx
    simp [standardRulingQuadric, (heU x).mpr hx]
  · intro x hx
    simp [standardRulingQuadric, (heV x).mpr hx]
  · intro x hx
    have he := (heW x).mpr hx
    simp [standardRulingQuadric, ← he, mul_comm]

end DimensionFourDependence
