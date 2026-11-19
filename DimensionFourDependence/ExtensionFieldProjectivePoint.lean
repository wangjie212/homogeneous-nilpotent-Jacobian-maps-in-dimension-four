import DimensionFourDependence.HomogeneousResidueSpecialization

/-! # Projective points with coordinates in an extension field

Their line kernels define points of the original projective spectrum.
In particular a residue field need not be identified with the constants
to obtain an actual point of a curve's projective closure.
-/

namespace DimensionFourDependence

open MvPolynomial Topology

attribute [local instance] MvPolynomial.gradedAlgebra

variable {E κ σ : Type*} [Field E] [Field κ] [Algebra E κ]

noncomputable def projectiveFieldPointMap (z : σ → κ) : MvPolynomial σ E →ₐ[E] Polynomial κ :=
  (Polynomial.mapAlgHom (aeval z)).comp gradeHom

theorem projectiveFieldPointMap_coeff (z : σ → κ) (P : MvPolynomial σ E) (d : ℕ) :
    (projectiveFieldPointMap (E := E) z P).coeff d = aeval z (homogeneousComponent d P) := by
  simp [projectiveFieldPointMap, coeff_gradeHom]

theorem projectiveFieldPointMap_homogeneous (z : σ → κ) {P : MvPolynomial σ E} {d : ℕ}
    (hP : P.IsHomogeneous d) :
    projectiveFieldPointMap (E := E) z P = Polynomial.monomial d (aeval z P) := by
  simp [projectiveFieldPointMap, gradeHom_of_isHomogeneous hP]

noncomputable def projectiveFieldPointIdeal (z : σ → κ) :
    HomogeneousIdeal (homogeneousSubmodule σ E) where
  toSubmodule := RingHom.ker (projectiveFieldPointMap (E := E) z)
  is_homogeneous' := by
    intro d P hP
    change projectiveFieldPointMap (E := E) z (MvPolynomial.decomposition.decompose' P d) = 0
    rw [MvPolynomial.decomposition.decompose'_apply,
      projectiveFieldPointMap_homogeneous z (homogeneousComponent_isHomogeneous d P),
      Polynomial.monomial_eq_zero_iff, ← projectiveFieldPointMap_coeff]
    change projectiveFieldPointMap (E := E) z P = 0 at hP
    rw [hP, Polynomial.coeff_zero]

/-- The actual point of `Proj E[X]` represented by extension-field coordinates. -/
noncomputable def projectiveFieldPoint (z : σ → κ) (hz : z ≠ 0) :
    ProjectiveSpectrum (homogeneousSubmodule σ E) where
  asHomogeneousIdeal := projectiveFieldPointIdeal (E := E) z
  isPrime := RingHom.ker_isPrime (projectiveFieldPointMap (E := E) z)
  not_irrelevant_le := by
    intro h
    obtain ⟨i, hi⟩ : ∃ i, z i ≠ 0 := by
      simpa only [ne_eq, funext_iff, Pi.zero_apply, not_forall] using hz
    have hx := h (HomogeneousIdeal.mem_irrelevant_of_mem _ (show 0 < (1 : ℕ) by omega)
      (isHomogeneous_X (R := E) i))
    change projectiveFieldPointMap (E := E) z (X i) = 0 at hx
    rw [projectiveFieldPointMap_homogeneous z (isHomogeneous_X (R := E) i),
      Polynomial.monomial_eq_zero_iff, aeval_X] at hx
    exact hi hx

/-- Extending the coordinates of an original rational point leaves the
underlying point of the original projective spectrum unchanged. -/
theorem projectiveFieldPoint_map_eq (z : σ → E) (hz : z ≠ 0)
    (hz' : (fun i => algebraMap E κ (z i)) ≠ 0) :
    projectiveFieldPoint (E := E) (fun i => algebraMap E κ (z i)) hz' = projectiveCoordinatePoint z hz := by
  apply ProjectiveSpectrum.ext
  apply HomogeneousIdeal.toIdeal_injective
  ext P
  change projectiveFieldPointMap (E := E) (fun i => algebraMap E κ (z i)) P = 0 ↔
    projectivePointLineMap z P = 0
  have he (d : ℕ) :
      (projectiveFieldPointMap (E := E) (fun i => algebraMap E κ (z i)) P).coeff d =
        algebraMap E κ ((projectivePointLineMap z P).coeff d) := by
    rw [projectiveFieldPointMap_coeff, projectivePointLineMap_coeff]
    exact (comp_aeval_apply z (Algebra.ofId E κ) (homogeneousComponent d P)).symm
  constructor
  · intro hP
    apply Polynomial.ext
    intro d
    apply (algebraMap E κ).injective
    rw [Polynomial.coeff_zero, map_zero, ← he, hP, Polynomial.coeff_zero]
  · intro hP
    apply Polynomial.ext
    intro d
    rw [Polynomial.coeff_zero, he, hP, Polynomial.coeff_zero, map_zero]

variable {O F : Type*} [CommRing O] [Field F] [Algebra E O] [Algebra E F]
    [Algebra O F] [IsScalarTower E O F]

/-- Reducing an integral common normalization gives an actual point
on the original projective closure, even with a larger residue field. -/
theorem residue_field_point_mem_projective_closure
    (π : O →ₐ[E] κ) (hinj : Function.Injective (algebraMap O F))
    (x : σ → F) (s : F) (z : Option σ → O)
    (hz : ∀ j, algebraMap O F (z j) = s * j.elim 1 x)
    (hres : (fun j => π (z j)) ≠ 0) :
    projectiveFieldPoint (E := E) (fun j => π (z j)) hres ∈ projectiveClosureSet (L := E) x := by
  have hc : projectiveClosureSet (L := E) x =
      ProjectiveSpectrum.zeroLocus (homogeneousSubmodule (Option σ) E)
        (projectiveConeIdeal (L := E) x : Set (MvPolynomial (Option σ) E)) := by
    change closure {projectiveClosureGenericPoint (L := E) x} =
      ProjectiveSpectrum.zeroLocus (homogeneousSubmodule (Option σ) E)
        ((projectiveClosureGenericPoint (L := E) x).asHomogeneousIdeal : Set _)
    rw [← ProjectiveSpectrum.vanishingIdeal_singleton]
    exact (ProjectiveSpectrum.zeroLocus_vanishingIdeal_eq_closure _ _).symm
  rw [hc]
  intro P hP
  change projectiveFieldPointMap (E := E) (fun j => π (z j)) P = 0
  apply Polynomial.ext
  intro d
  rw [projectiveFieldPointMap_coeff, Polynomial.coeff_zero]
  apply homogeneous_residue_specialization π hinj (fun j : Option σ => j.elim 1 x) s z hz
    (homogeneousComponent d P) (homogeneousComponent_isHomogeneous d P)
  exact (projectiveConeIdeal_mem_of_isHomogeneous x (homogeneousComponent_isHomogeneous d P)).mp
    (projectiveConeIdeal_homogeneousComponent_mem x hP d)

end DimensionFourDependence
