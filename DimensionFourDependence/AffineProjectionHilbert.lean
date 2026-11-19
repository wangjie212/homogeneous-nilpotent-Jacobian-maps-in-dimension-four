import DimensionFourDependence.CoordinateProjectionHilbert
import DimensionFourDependence.GradedSurjectiveHilbertTransport
import DimensionFourDependence.HomogenizeChart

/-! # Affine-linear projections do not increase the actual Hilbert function

Homogenize each specified affine-linear coordinate to degree one. Its
graded pullback factors the actual chart evaluations, so the image of
each projected homogeneous piece is a subspace of the original image.
-/

namespace DimensionFourDependence

open MvPolynomial Module

variable {L F sigma tau : Type*} [Field L] [Field F] [Algebra L F]

/-- The actual projective pullback of specified affine polynomial coordinates. -/
noncomputable def projectiveAffinePolynomialPullback (p : tau → MvPolynomial sigma L) :
    MvPolynomial (Option tau) L →ₐ[L] MvPolynomial (Option sigma) L :=
  aeval (fun j : Option tau => j.elim (X none) (fun i => projectiveHomogenize (p i) 1))

/-- Affine-linear projected coordinates give a degree-preserving
actual projective pullback. -/
theorem projectiveAffinePolynomialPullback_homogeneous
    (p : tau → MvPolynomial sigma L) (hp : ∀ i, (p i).totalDegree ≤ 1)
    (P : MvPolynomial (Option tau) L) {d : ℕ} (hP : P.IsHomogeneous d) :
    (projectiveAffinePolynomialPullback p P).IsHomogeneous d := by
  have hvars : ∀ j : Option tau,
      (j.elim (X none) (fun i => projectiveHomogenize (p i) 1)).IsHomogeneous 1 := by
    intro j
    cases j with
    | none => exact isHomogeneous_X L none
    | some i => exact projectiveHomogenize_isHomogeneous (p i) 1 (hp i)
  simpa only [one_mul, projectiveAffinePolynomialPullback] using hP.aeval _ hvars

/-- Evaluation on the actual projected affine point agrees with
evaluation of its homogeneous pullback on the original affine point. -/
theorem projectiveAffinePolynomialPullback_aeval
    (x : sigma → F) (p : tau → MvPolynomial sigma L) :
    (aeval (fun j : Option sigma => j.elim 1 x)).comp (projectiveAffinePolynomialPullback p) =
      aeval (fun j : Option tau => j.elim 1 (fun i => aeval x (p i))) := by
  apply MvPolynomial.algHom_ext
  intro j
  cases j with
  | none => simp [projectiveAffinePolynomialPullback]
  | some i =>
    simp only [AlgHom.comp_apply, projectiveAffinePolynomialPullback, aeval_X, Option.elim_some]
    exact projectiveHomogenize_aeval_chart (p i) 1 x

/-- The actual chart evaluation on each projected homogeneous piece
factors through the actual homogeneous pullback. -/
theorem homogeneousChartEvaluation_affine_projection
    (x : sigma → F) (p : tau → MvPolynomial sigma L) (hp : ∀ i, (p i).totalDegree ≤ 1) (d : ℕ) :
    homogeneousChartEvaluation (L := L) (fun i => aeval x (p i)) d =
      (homogeneousChartEvaluation (L := L) x d).comp
        (homogeneousPolynomialAlgebraMap (projectiveAffinePolynomialPullback p)
          (fun _ P hP => projectiveAffinePolynomialPullback_homogeneous p hp P hP) d) := by
  apply LinearMap.ext
  intro P
  exact (DFunLike.congr_fun (projectiveAffinePolynomialPullback_aeval x p)
    (P : MvPolynomial (Option tau) L)).symm

/-- Taking any specified affine-linear polynomial coordinates cannot
increase the actual projective closure Hilbert function. -/
theorem projectiveHilbertFunction_affine_projection_le [Finite sigma]
    (x : sigma → F) (p : tau → MvPolynomial sigma L) (hp : ∀ i, (p i).totalDegree ≤ 1) (d : ℕ) :
    projectiveHilbertFunction (projectiveConeIdeal (L := L) (fun i => aeval x (p i))) d ≤
      projectiveHilbertFunction (projectiveConeIdeal (L := L) x) d := by
  rw [projectiveHilbertFunction_cone_eq_chart_rank, projectiveHilbertFunction_cone_eq_chart_rank,
    homogeneousChartEvaluation_affine_projection x p hp]
  exact Submodule.finrank_mono (LinearMap.range_comp_le_range _ _)

end DimensionFourDependence
