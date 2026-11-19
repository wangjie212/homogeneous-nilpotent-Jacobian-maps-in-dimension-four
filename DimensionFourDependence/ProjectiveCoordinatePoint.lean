import DimensionFourDependence.SaturatedRadialMap

/-! # Projective points represented by nonzero coordinate vectors

The kernel of evaluation along the line `t z` is a homogeneous relevant
prime. This gives an actual point of Mathlib's projective spectrum,
including points in the boundary chart of an affine projective closure.
-/

namespace DimensionFourDependence

open MvPolynomial Topology

attribute [local instance] MvPolynomial.gradedAlgebra

variable {E σ : Type*} [Field E]

/-- Evaluation on the parametrized line through a coordinate vector. -/
noncomputable def projectivePointLineMap (z : σ → E) :
    MvPolynomial σ E →ₐ[E] Polynomial E :=
  (Polynomial.mapAlgHom (aeval z)).comp gradeHom

theorem projectivePointLineMap_coeff (z : σ → E) (p : MvPolynomial σ E) (d : ℕ) :
    (projectivePointLineMap z p).coeff d = aeval z (homogeneousComponent d p) := by
  simp [projectivePointLineMap, coeff_gradeHom]

theorem projectivePointLineMap_homogeneous (z : σ → E)
    {p : MvPolynomial σ E} {d : ℕ} (hp : p.IsHomogeneous d) :
    projectivePointLineMap z p = Polynomial.monomial d (aeval z p) := by
  simp [projectivePointLineMap, gradeHom_of_isHomogeneous hp]

/-- The homogeneous prime of the line through `z`. -/
noncomputable def projectivePointLineIdeal (z : σ → E) :
    HomogeneousIdeal (homogeneousSubmodule σ E) where
  toSubmodule := RingHom.ker (projectivePointLineMap z)
  is_homogeneous' := by
    intro d p hp
    change projectivePointLineMap z (MvPolynomial.decomposition.decompose' p d) = 0
    rw [MvPolynomial.decomposition.decompose'_apply, projectivePointLineMap_homogeneous z
      (homogeneousComponent_isHomogeneous d p), Polynomial.monomial_eq_zero_iff]
    rw [← projectivePointLineMap_coeff]
    change projectivePointLineMap z p = 0 at hp
    rw [hp, Polynomial.coeff_zero]

/-- The actual projective-spectrum point represented by a nonzero vector. -/
noncomputable def projectiveCoordinatePoint (z : σ → E) (hz : z ≠ 0) :
    ProjectiveSpectrum (homogeneousSubmodule σ E) where
  asHomogeneousIdeal := projectivePointLineIdeal z
  isPrime := RingHom.ker_isPrime (projectivePointLineMap z)
  not_irrelevant_le := by
    intro h
    obtain ⟨i, hi⟩ : ∃ i, z i ≠ 0 := by
      simpa only [ne_eq, funext_iff, Pi.zero_apply, not_forall] using hz
    have hx := h (HomogeneousIdeal.mem_irrelevant_of_mem _ (show 0 < (1 : ℕ) by omega)
      (isHomogeneous_X (R := E) i))
    change projectivePointLineMap z (X i) = 0 at hx
    rw [projectivePointLineMap_homogeneous z (isHomogeneous_X (R := E) i),
      Polynomial.monomial_eq_zero_iff, aeval_X] at hx
    exact hi hx

/-- A homogeneous equation belongs to the coordinate point exactly when
it vanishes on its representing vector. -/
theorem projectiveCoordinatePoint_mem_homogeneous (z : σ → E) (hz : z ≠ 0)
    {p : MvPolynomial σ E} {d : ℕ} (hp : p.IsHomogeneous d) :
    p ∈ (projectiveCoordinatePoint z hz).asHomogeneousIdeal ↔ aeval z p = 0 := by
  change projectivePointLineMap z p = 0 ↔ _
  rw [projectivePointLineMap_homogeneous z hp, Polynomial.monomial_eq_zero_iff]

/-- Homogeneous equations of an actual affine closure vanish at every
coordinate point of that closure, including points at infinity. -/
theorem projectiveClosureSet_coordinate_equation
    {F : Type*} [Field F] [Algebra E F] (x : σ → F)
    (z : Option σ → E) (hz : z ≠ 0)
    (hpoint : projectiveCoordinatePoint z hz ∈ projectiveClosureSet (L := E) x)
    {p : MvPolynomial (Option σ) E} {d : ℕ} (hp : p.IsHomogeneous d)
    (hvan : p ∈ projectiveConeIdeal (L := E) x) : aeval z p = 0 := by
  have hc : projectiveClosureSet (L := E) x =
      ProjectiveSpectrum.zeroLocus (homogeneousSubmodule (Option σ) E)
        (projectiveConeIdeal (L := E) x : Set (MvPolynomial (Option σ) E)) := by
    change closure {projectiveClosureGenericPoint (L := E) x} =
      ProjectiveSpectrum.zeroLocus (homogeneousSubmodule (Option σ) E)
        ((projectiveClosureGenericPoint (L := E) x).asHomogeneousIdeal : Set _)
    rw [← ProjectiveSpectrum.vanishingIdeal_singleton]
    exact (ProjectiveSpectrum.zeroLocus_vanishingIdeal_eq_closure _ _).symm
  rw [hc] at hpoint
  exact (projectiveCoordinatePoint_mem_homogeneous z hz hp).mp (hpoint hvan)

end DimensionFourDependence
