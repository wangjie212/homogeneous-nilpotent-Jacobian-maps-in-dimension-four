import DimensionFourDependence.ExtendedProjectiveInfinityChart
import DimensionFourDependence.HomogeneousProjectiveSubstitution

/-! # Actual boundary points under coordinate projection and proportionality

The homogeneous line maps commute with the original coordinate
selection. Thus a projection with nonzero boundary vector is an actual
point of the projected closure. Over the original coefficient field,
nonzero proportional extension-valued directions remain the same
projective point.
-/

namespace DimensionFourDependence

open MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra

variable {E F G sigma tau : Type*} [Field E] [Field F] [Field G] [Algebra E F] [Algebra E G]

/-- Coordinate-vector equality gives equality of actual projective
points independently of the two nonzero-coordinate proof witnesses. -/
theorem projectiveFieldPoint_eq_of_coordinate_eq
    (z w : sigma → F) (hz : z ≠ 0) (hw : w ≠ 0) (he : z = w) :
    projectiveFieldPoint (E := E) z hz = projectiveFieldPoint (E := E) w hw := by
  cases he
  rfl

/-- The actual affine projective closure is the zero locus of its
entire original homogeneous relation ideal. -/
theorem projectiveClosureSet_eq_zeroLocus_cone (x : sigma → G) :
    projectiveClosureSet (L := E) x =
      ProjectiveSpectrum.zeroLocus (homogeneousSubmodule (Option sigma) E)
        (projectiveConeIdeal (L := E) x : Set _) := by
  change closure {projectiveClosureGenericPoint (L := E) x} =
    ProjectiveSpectrum.zeroLocus (homogeneousSubmodule (Option sigma) E)
      ((projectiveClosureGenericPoint (L := E) x).asHomogeneousIdeal : Set _)
  rw [← ProjectiveSpectrum.vanishingIdeal_singleton]
  exact (ProjectiveSpectrum.zeroLocus_vanishingIdeal_eq_closure _ _).symm

/-- The original homogeneous cone line map commutes with every
specified selection of affine coordinates. -/
theorem projectiveConeMap_coordinate_projection
    (x : sigma → G) (f : tau → sigma) (P : MvPolynomial (Option tau) E) :
    projectiveConeMap (L := E) x (rename (Option.map f) P) =
      projectiveConeMap (L := E) (x ∘ f) P := by
  have he : (projectiveConeMap (L := E) x).comp (rename (Option.map f)) =
      projectiveConeMap (L := E) (x ∘ f) := by
    apply MvPolynomial.algHom_ext
    intro j
    cases j <;> simp [projectiveConeMap_X]
  exact DFunLike.congr_fun he P

/-- The actual extension-valued point line map commutes with the
same specified coordinate selection, including all inhomogeneous forms. -/
theorem projectiveFieldPointMap_coordinate_projection
    (z : sigma → F) (f : tau → sigma) (P : MvPolynomial tau E) :
    projectiveFieldPointMap (E := E) z (rename f P) = projectiveFieldPointMap (E := E) (z ∘ f) P := by
  have he : (projectiveFieldPointMap (E := E) z).comp (rename f) =
      projectiveFieldPointMap (E := E) (z ∘ f) := by
    apply MvPolynomial.algHom_ext
    intro j
    simp [projectiveFieldPointMap, gradeHom]
  exact DFunLike.congr_fun he P

/-- A nonzero coordinate projection of an actual closure point is
an actual projective point of the closure of the selected affine coordinates. -/
theorem projective_closure_point_coordinate_projection
    (x : sigma → G) (z : Option sigma → F) (hz : z ≠ 0)
    (hpoint : projectiveFieldPoint (E := E) z hz ∈ projectiveClosureSet (L := E) x)
    (f : tau → sigma) (hf : z ∘ Option.map f ≠ 0) :
    projectiveFieldPoint (E := E) (z ∘ Option.map f) hf ∈ projectiveClosureSet (L := E) (x ∘ f) := by
  rw [projectiveClosureSet_eq_zeroLocus_cone] at hpoint ⊢
  intro P hP
  have hrename : rename (Option.map f) P ∈ projectiveConeIdeal (L := E) x := by
    change projectiveConeMap (L := E) x (rename (Option.map f) P) = 0
    rw [projectiveConeMap_coordinate_projection]
    exact hP
  have he := hpoint hrename
  change projectiveFieldPointMap (E := E) z (rename (Option.map f) P) = 0 at he
  change projectiveFieldPointMap (E := E) (z ∘ Option.map f) P = 0
  rwa [projectiveFieldPointMap_coordinate_projection] at he

/-- Nonzero proportional extension-valued infinity directions
transfer membership in the original coefficient-field projective closure. -/
theorem projective_closure_extension_infinity_point_of_nonzero_smul
    (x : Fin 3 → G) (v b : Fin 3 → F) (hv : v ≠ 0)
    (hpoint : projectiveFieldPoint (E := E) (fun j : Option (Fin 3) => j.elim 0 v)
      (infinity_direction_projective_coordinates_ne_zero v hv) ∈ projectiveClosureSet (L := E) x)
    (t : F) (ht : t ≠ 0) (hrep : v = t • b) :
    ∃ hb : b ≠ 0,
      projectiveFieldPoint (E := E) (fun j : Option (Fin 3) => j.elim 0 b)
        (infinity_direction_projective_coordinates_ne_zero b hb) ∈ projectiveClosureSet (L := E) x := by
  have hb : b ≠ 0 := by
    intro hzero
    apply hv
    rw [hrep, hzero, smul_zero]
  refine ⟨hb, ?_⟩
  have he := projectiveFieldPoint_eq_of_proportional (K := E)
    (fun j : Option (Fin 3) => j.elim 0 v) (fun j : Option (Fin 3) => j.elim 0 b)
    (infinity_direction_projective_coordinates_ne_zero v hv)
    (infinity_direction_projective_coordinates_ne_zero b hb) t ht (by
      intro j
      cases j with
      | none => simp
      | some i => exact congrFun hrep i)
  rwa [he] at hpoint

end DimensionFourDependence
