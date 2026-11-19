import DimensionFourDependence.GradedSurjectiveHilbertTransport
import DimensionFourDependence.HomogeneousProjectiveSubstitution
import DimensionFourDependence.GraphHilbert

/-! # Radial projection preserves degree on a nonzero affine hyperplane

A homogeneous linear form with nonzero constant value on the actual
affine curve recovers its homogenizing coordinate by a linear expression
in the original source coordinates. The resulting graded polynomial
map is onto in every degree and identifies the entire original relation
ideals. Thus radial projection to the original projective source space
preserves every actual Hilbert quotient dimension and its curve degree.
-/

namespace DimensionFourDependence

open MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra

variable {L F sigma : Type*} [Field L] [Field F] [Algebra L F]

/-- Eliminate the affine homogenizing coordinate using the specified
nonzero original affine-hyperplane constant. -/
noncomputable def nonzeroHyperplaneRadialPullback (S : MvPolynomial sigma L) (c : L) :
    MvPolynomial (Option sigma) L →ₐ[L] MvPolynomial sigma L :=
  aeval (fun j : Option sigma => j.elim (C c⁻¹ * S) X)

/-- The original direction-coordinate inclusion is an actual right inverse. -/
theorem nonzeroHyperplaneRadialPullback_rename
    (S : MvPolynomial sigma L) (c : L) (P : MvPolynomial sigma L) :
    nonzeroHyperplaneRadialPullback S c (rename some P) = P := by
  have he : (nonzeroHyperplaneRadialPullback S c).comp (rename some) = AlgHom.id L _ := by
    apply MvPolynomial.algHom_ext
    intro i
    simp [nonzeroHyperplaneRadialPullback]
  exact DFunLike.congr_fun he P

/-- A linear hyperplane equation gives a degree-preserving actual pullback. -/
theorem nonzeroHyperplaneRadialPullback_homogeneous
    (S : MvPolynomial sigma L) (hS : S.IsHomogeneous 1) (c : L)
    (P : MvPolynomial (Option sigma) L) {d : ℕ} (hP : P.IsHomogeneous d) :
    (nonzeroHyperplaneRadialPullback S c P).IsHomogeneous d := by
  have hvars : ∀ j : Option sigma, (j.elim (C c⁻¹ * S) X).IsHomogeneous 1 := by
    intro j
    cases j with
    | none =>
      change (C c⁻¹ * S).IsHomogeneous 1
      simpa only [zero_add] using (isHomogeneous_C (R := L) (σ := sigma) c⁻¹).mul hS
    | some i => exact isHomogeneous_X L i
  simpa only [one_mul, nonzeroHyperplaneRadialPullback] using hP.aeval _ hvars

/-- The radial pullback is onto the entire original polynomial ring. -/
theorem nonzeroHyperplaneRadialPullback_surjective (S : MvPolynomial sigma L) (c : L) :
    Function.Surjective (nonzeroHyperplaneRadialPullback S c) :=
  fun P => ⟨rename some P, nonzeroHyperplaneRadialPullback_rename S c P⟩

/-- It is onto every actual homogeneous degree, retaining the
specified original direction-coordinate section. -/
theorem nonzeroHyperplaneRadialPullback_homogeneous_surjective
    (S : MvPolynomial sigma L) (hS : S.IsHomogeneous 1) (c : L) (d : ℕ) :
    Function.Surjective (homogeneousPolynomialAlgebraMap (nonzeroHyperplaneRadialPullback S c)
      (fun _ P hP => nonzeroHyperplaneRadialPullback_homogeneous S hS c P hP) d) := by
  intro P
  refine ⟨⟨rename some (P : MvPolynomial sigma L), P.property.rename_isHomogeneous⟩, ?_⟩
  apply Subtype.ext
  change nonzeroHyperplaneRadialPullback S c
    (rename (some : sigma → Option sigma) (P : MvPolynomial sigma L)) = (P : MvPolynomial sigma L)
  exact nonzeroHyperplaneRadialPullback_rename S c P

/-- The actual affine projective-closure line map factors through
the actual radial projective-point line map, on the entire polynomial ring. -/
theorem projectiveConeMap_nonzero_hyperplane_radial_factor
    (S : MvPolynomial sigma L) (hS : S.IsHomogeneous 1) (c : L) (hc : c ≠ 0)
    (x : sigma → F) (hvalue : aeval x S = algebraMap L F c) :
    projectiveConeMap (L := L) x =
      (projectiveFieldPointMap (E := L) x).comp (nonzeroHyperplaneRadialPullback S c) := by
  apply MvPolynomial.algHom_ext
  intro j
  cases j with
  | none =>
    simp only [projectiveConeMap_X, Option.elim_none, Polynomial.C_1, one_mul,
      AlgHom.comp_apply, nonzeroHyperplaneRadialPullback, aeval_X, map_mul]
    rw [projectiveFieldPointMap_homogeneous x hS, hvalue]
    simpa [hc] using (Polynomial.X_pow_eq_monomial (R := F) (n := 1))
  | some i =>
    simp only [projectiveConeMap_X, Option.elim_some, AlgHom.comp_apply,
      nonzeroHyperplaneRadialPullback, aeval_X]
    simp [projectiveFieldPointMap, gradeHom]

/-- The entire actual affine closure ideal is the preimage of the
entire actual radial projective-source ideal. -/
theorem projectiveConeIdeal_nonzero_hyperplane_radial_comap
    (S : MvPolynomial sigma L) (hS : S.IsHomogeneous 1) (c : L) (hc : c ≠ 0)
    (x : sigma → F) (hvalue : aeval x S = algebraMap L F c) :
    projectiveConeIdeal (L := L) x =
      (projectiveFieldPointIdeal (E := L) x).toIdeal.comap (nonzeroHyperplaneRadialPullback S c).toRingHom := by
  ext P
  change projectiveConeMap (L := L) x P = 0 ↔
    projectiveFieldPointMap (E := L) x (nonzeroHyperplaneRadialPullback S c P) = 0
  rw [projectiveConeMap_nonzero_hyperplane_radial_factor S hS c hc x hvalue]
  rfl

/-- The actual graded coordinate elimination maps onto the entire
actual radial projective-source relation ideal. -/
theorem projectiveConeIdeal_nonzero_hyperplane_radial_map
    (S : MvPolynomial sigma L) (hS : S.IsHomogeneous 1) (c : L) (hc : c ≠ 0)
    (x : sigma → F) (hvalue : aeval x S = algebraMap L F c) :
    (projectiveConeIdeal (L := L) x).map (nonzeroHyperplaneRadialPullback S c).toRingHom =
      (projectiveFieldPointIdeal (E := L) x).toIdeal := by
  rw [projectiveConeIdeal_nonzero_hyperplane_radial_comap S hS c hc x hvalue]
  exact Ideal.map_comap_of_surjective _ (nonzeroHyperplaneRadialPullback_surjective S c) _

/-- Radial projection on an actual nonzero affine hyperplane
preserves every actual original homogeneous quotient dimension. -/
theorem projectiveHilbertFunction_nonzero_hyperplane_radial
    (S : MvPolynomial sigma L) (hS : S.IsHomogeneous 1) (c : L) (hc : c ≠ 0)
    (x : sigma → F) (hvalue : aeval x S = algebraMap L F c) (d : ℕ) :
    projectiveHilbertFunction (projectiveConeIdeal (L := L) x) d =
      projectiveHilbertFunction (projectiveFieldPointIdeal (E := L) x).toIdeal d := by
  have hker : RingHom.ker (nonzeroHyperplaneRadialPullback S c).toRingHom ≤
      projectiveConeIdeal (L := L) x := by
    rw [projectiveConeIdeal_nonzero_hyperplane_radial_comap S hS c hc x hvalue]
    intro P hP
    change nonzeroHyperplaneRadialPullback S c P ∈ (projectiveFieldPointIdeal (E := L) x).toIdeal
    change nonzeroHyperplaneRadialPullback S c P = 0 at hP
    rw [hP]
    exact Ideal.zero_mem _
  have he := projectiveHilbertFunction_surjective_graded_map (nonzeroHyperplaneRadialPullback S c)
    (fun _ P hP => nonzeroHyperplaneRadialPullback_homogeneous S hS c P hP)
    (nonzeroHyperplaneRadialPullback_surjective S c)
    (nonzeroHyperplaneRadialPullback_homogeneous_surjective S hS c)
    (projectiveConeIdeal (L := L) x) hker d
  rwa [projectiveConeIdeal_nonzero_hyperplane_radial_map S hS c hc x hvalue] at he

/-- The original affine closure and its actual radial projective
source image have exactly the same actual positive Hilbert degree. -/
theorem curveHilbertDegree_nonzero_hyperplane_radial
    (S : MvPolynomial sigma L) (hS : S.IsHomogeneous 1) (c : L) (hc : c ≠ 0)
    (x : sigma → F) (hvalue : aeval x S = algebraMap L F c) (e : ℕ) :
    HasCurveHilbertDegree (projectiveConeIdeal (L := L) x) e ↔
      HasCurveHilbertDegree (projectiveFieldPointIdeal (E := L) x).toIdeal e := by
  simp only [HasCurveHilbertDegree, projectiveHilbertFunction_nonzero_hyperplane_radial S hS c hc x hvalue]

end DimensionFourDependence
