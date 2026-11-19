import DimensionFourDependence.AffineProjectionHilbert
import DimensionFourDependence.AffinePrincipalCone
import DimensionFourDependence.PlaneEquationDegreeBound

/-! # A bounded-degree generator for an actual affine plane projection

Keep the entire affine relation ideal of two specified affine-linear
source coordinates. One transcendental coordinate makes it principal.
The actual projected Hilbert bound controls its generator's total degree.
-/

namespace DimensionFourDependence

open MvPolynomial

variable {L F sigma : Type*} [Field L] [Field F] [Algebra L F]

/-- A plane projection with a transcendental coordinate has an actual
nonzero affine relation generator of degree at most the original curve's
Hilbert degree. Both its nonvanishing and degree are derived. -/
theorem affine_plane_projection_exists_bounded_relation_generator [Finite sigma]
    (x : sigma → F) (p : Option Unit → MvPolynomial sigma L)
    (hp : ∀ i, (p i).totalDegree ≤ 1) (ht : Transcendental L (aeval x (p (some ()))))
    {e : ℕ} (he : HasCurveHilbertDegree (projectiveConeIdeal (L := L) x) e) :
    ∃ Q : MvPolynomial (Option Unit) L, Q ≠ 0 ∧ Q.totalDegree ≤ e ∧
      RingHom.ker (aeval (fun i => aeval x (p i)) : MvPolynomial (Option Unit) L →ₐ[L] F) = Ideal.span {Q} := by
  let pair : Option Unit → F := fun i => aeval x (p i)
  have hpairs : (fun j : Option Unit => j.elim (pair none) (fun _ => pair (some ()))) = pair := by
    funext j
    cases j with
    | none => rfl
    | some u => cases u; rfl
  obtain ⟨Q, hQker⟩ := two_coordinate_relation_exists_generator (pair (some ())) (pair none) ht
  rw [hpairs] at hQker
  let P := projectiveHomogenize Q Q.totalDegree
  have hP : P.IsHomogeneous Q.totalDegree := projectiveHomogenize_isHomogeneous Q _ le_rfl
  have hcone : projectiveConeIdeal (L := L) pair = Ideal.span {P} :=
    projectiveConeIdeal_eq_homogenized_affine_generator pair Q hQker
  have hcard : Nat.card (Option (Option Unit)) = 3 := by simp
  have hbound : ∀ n, projectiveHilbertFunction (Ideal.span {P}) n ≤
      projectiveHilbertFunction (projectiveConeIdeal (L := L) x) n := by
    intro n
    rw [← hcone]
    exact projectiveHilbertFunction_affine_projection_le x p hp n
  have hP0 := plane_principal_equation_ne_zero_of_curve_hilbert_bound hcard P _ he hbound
  have hQ0 : Q ≠ 0 := by
    intro hzero
    apply hP0
    change projectiveHomogenize Q Q.totalDegree = 0
    rw [hzero, projectiveHomogenize_zero]
  exact ⟨Q, hQ0, plane_principal_equation_degree_le_curve_degree hcard P hP hP0 _ he hbound, hQker⟩

end DimensionFourDependence
