import DimensionFourDependence.ProjectivePrimeBaseExtension
import DimensionFourDependence.ProjectiveBoundaryProjection

/-! # The constructed fixed infinity support is an actual point of the section

An actual original-coefficient boundary point contains the entire
coefficient-extended closure ideal, by the original homogeneous point
line map. Its vanishing infinity coordinate includes the entire infinity
section ideal. A proved single-point support upper bound therefore
identifies that actual point with the specified fixed point, proving
membership as well as uniqueness without assuming nonemptiness.
-/

namespace DimensionFourDependence

open MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra

variable {E F G sigma : Type*} [Field E] [Field F] [Field G] [Algebra E F] [Algebra E G]

/-- An actual point of the original closure contains the entire
specified coefficient extension of its original homogeneous ideal. -/
theorem original_closure_point_contains_extended_cone
    (x : sigma → G) (v : Option sigma → F) (hv : v ≠ 0)
    (hpoint : projectiveFieldPoint (E := E) v hv ∈ projectiveClosureSet (L := E) x) :
    Ideal.map (MvPolynomial.map (algebraMap E F)) (projectiveConeIdeal (L := E) x) ≤
      (projectiveFieldPoint (E := F) v hv).asHomogeneousIdeal.toIdeal := by
  rw [projectiveClosureSet_eq_zeroLocus_cone] at hpoint
  apply Ideal.map_le_iff_le_comap.mpr
  intro P hP
  change projectiveFieldPointMap (E := F) v (MvPolynomial.map (algebraMap E F) P) = 0
  rw [projectiveFieldPointMap_coefficient_extension]
  exact hpoint hP

/-- An original closure point at infinity is an actual point of
the entire coefficient-extended infinity-section ideal. -/
theorem original_infinity_point_contains_extended_section
    (x : sigma → G) (v : Option sigma → F) (hv : v ≠ 0)
    (hpoint : projectiveFieldPoint (E := E) v hv ∈ projectiveClosureSet (L := E) x)
    (hinfinity : v none = 0) :
    Ideal.map (MvPolynomial.map (algebraMap E F)) (projectiveConeIdeal (L := E) x) ⊔
      Ideal.span ({X none} : Set (MvPolynomial (Option sigma) F)) ≤
        (projectiveFieldPoint (E := F) v hv).asHomogeneousIdeal.toIdeal := by
  apply sup_le
  · exact original_closure_point_contains_extended_cone x v hv hpoint
  · apply Ideal.span_le.mpr
    rintro _ rfl
    change projectiveFieldPointMap (E := F) v (X none) = 0
    simp [projectiveFieldPointMap, gradeHom, hinfinity]

/-- The actual original boundary point proves that the fixed point
in a single-support upper bound belongs to the entire actual section. -/
theorem original_boundary_constructs_fixed_support_membership
    (x : sigma → G) (v : Option sigma → F) (hv : v ≠ 0)
    (hpoint : projectiveFieldPoint (E := E) v hv ∈ projectiveClosureSet (L := E) x)
    (hinfinity : v none = 0)
    (s0 : ProjectiveSpectrum (homogeneousSubmodule (Option sigma) F))
    (hsupport : ∀ s : ProjectiveSpectrum (homogeneousSubmodule (Option sigma) F),
      Ideal.map (MvPolynomial.map (algebraMap E F)) (projectiveConeIdeal (L := E) x) ⊔
        Ideal.span ({X none} : Set (MvPolynomial (Option sigma) F)) ≤ s.asHomogeneousIdeal.toIdeal → s = s0) :
    Ideal.map (MvPolynomial.map (algebraMap E F)) (projectiveConeIdeal (L := E) x) ⊔
      Ideal.span ({X none} : Set (MvPolynomial (Option sigma) F)) ≤ s0.asHomogeneousIdeal.toIdeal := by
  have hmem := original_infinity_point_contains_extended_section x v hv hpoint hinfinity
  rw [← hsupport _ hmem]
  exact hmem

end DimensionFourDependence
