import DimensionFourDependence.ImageHypersurface

/-! # The actual image hypersurface in the projective spectrum

The homogeneous prime of output relations gives the generic image point
in Mathlib's projective spectrum. Its closure is irreducible, has exactly
that prime as its vanishing ideal, and in rank three equals the zero
locus of the constructed irreducible homogeneous equation.
-/

namespace DimensionFourDependence

open MvPolynomial Topology

attribute [local instance] MvPolynomial.gradedAlgebra

variable {K : Type*} [Field K]

/-- The image prime is homogeneous for a map of positive homogeneous degree. -/
theorem imageRelationIdeal_isHomogeneous
    (H : Fin 4 → MvPolynomial (Fin 4) K) {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d) :
    (imageRelationIdeal H).IsHomogeneous (homogeneousSubmodule (Fin 4) K) := by
  intro e R hR
  change aeval H (MvPolynomial.decomposition.decompose' R e : MvPolynomial (Fin 4) K) = 0
  simpa only [MvPolynomial.decomposition.decompose'_apply] using
    homogeneousComponent_relation H hd hH R hR e

/-- The actual homogeneous prime of the projective image. -/
noncomputable def imageHomogeneousIdeal
    (H : Fin 4 → MvPolynomial (Fin 4) K) {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d) :
    HomogeneousIdeal (homogeneousSubmodule (Fin 4) K) where
  toSubmodule := imageRelationIdeal H
  is_homogeneous' := imageRelationIdeal_isHomogeneous H hd hH

/-- The generic image point determined by the actual output relations. -/
noncomputable def projectiveImageGenericPoint
    (H : Fin 4 → MvPolynomial (Fin 4) K) {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d)
    (hH0 : H ≠ 0) : ProjectiveSpectrum (homogeneousSubmodule (Fin 4) K) where
  asHomogeneousIdeal := imageHomogeneousIdeal H hd hH
  isPrime := imageRelationIdeal_isPrime H
  not_irrelevant_le := by
    intro hle
    obtain ⟨i, hi⟩ : ∃ i, H i ≠ 0 := by
      simpa only [ne_eq, funext_iff, Pi.zero_apply, not_forall] using hH0
    have hx := hle (HomogeneousIdeal.mem_irrelevant_of_mem _ (show 0 < (1 : ℕ) by omega)
      (isHomogeneous_X (R := K) i))
    change aeval H (X i) = 0 at hx
    exact hi (by simpa only [aeval_X] using hx)

/-- The projective image closure represented by its actual relation prime. -/
noncomputable def projectiveImageSet
    (H : Fin 4 → MvPolynomial (Fin 4) K) {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d)
    (hH0 : H ≠ 0) : Set (ProjectiveSpectrum (homogeneousSubmodule (Fin 4) K)) :=
  closure {projectiveImageGenericPoint H hd hH hH0}

theorem projectiveImageSet_isIrreducible
    (H : Fin 4 → MvPolynomial (Fin 4) K) {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d)
    (hH0 : H ≠ 0) : IsIrreducible (projectiveImageSet H hd hH hH0) :=
  isIrreducible_singleton.closure

/-- The projective image closure has exactly the actual output relation ideal. -/
theorem projectiveImageSet_vanishingIdeal
    (H : Fin 4 → MvPolynomial (Fin 4) K) {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d)
    (hH0 : H ≠ 0) :
    (ProjectiveSpectrum.vanishingIdeal (projectiveImageSet H hd hH hH0)).toIdeal = imageRelationIdeal H := by
  change (ProjectiveSpectrum.vanishingIdeal (closure {projectiveImageGenericPoint H hd hH hH0})).toIdeal = _
  rw [ProjectiveSpectrum.vanishingIdeal_closure, ProjectiveSpectrum.vanishingIdeal_singleton]
  rfl

/-- In rank three the projective image is the actual irreducible hypersurface. -/
theorem projectiveImageSet_eq_hypersurface [CharZero K]
    (H : Fin 4 → MvPolynomial (Fin 4) K) {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d)
    (hH0 : H ≠ 0) (hrank : polyRank (jac H) = 3) (W : ImageRelationWitness H) :
    projectiveImageSet H hd hH hH0 =
      ProjectiveSpectrum.zeroLocus (homogeneousSubmodule (Fin 4) K) {W.equation} := by
  have hc : ProjectiveSpectrum.zeroLocus (homogeneousSubmodule (Fin 4) K)
      (imageRelationIdeal H : Set (MvPolynomial (Fin 4) K)) = projectiveImageSet H hd hH hH0 := by
    change ProjectiveSpectrum.zeroLocus (homogeneousSubmodule (Fin 4) K)
      ((projectiveImageGenericPoint H hd hH hH0).asHomogeneousIdeal : Set (MvPolynomial (Fin 4) K)) = _
    rw [← ProjectiveSpectrum.vanishingIdeal_singleton]
    exact ProjectiveSpectrum.zeroLocus_vanishingIdeal_eq_closure _ _
  rw [← hc, W.ideal_eq_span H hrank, ProjectiveSpectrum.zeroLocus_span]

/-- All hypersurface data are constructed from the original homogeneous
nilpotent rank-three assumptions. -/
theorem exists_projective_image_hypersurface [CharZero K]
    (H : Fin 4 → MvPolynomial (Fin 4) K) {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d)
    (hH0 : H ≠ 0) (hN : IsNilpotent (jac H)) (hrank : polyRank (jac H) = 3) :
    ∃ W : ImageRelationWitness H, projectiveImageSet H hd hH hH0 =
      ProjectiveSpectrum.zeroLocus (homogeneousSubmodule (Fin 4) K) {W.equation} := by
  obtain ⟨W⟩ := exists_image_relation_witness H hd hH hN
  exact ⟨W, projectiveImageSet_eq_hypersurface H hd hH hH0 hrank W⟩

end DimensionFourDependence
