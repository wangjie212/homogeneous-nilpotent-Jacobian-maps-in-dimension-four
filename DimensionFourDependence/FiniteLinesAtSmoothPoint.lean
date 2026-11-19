import DimensionFourDependence.HypersurfaceTangentPlane
import DimensionFourDependence.PlaneLineFinitenessTransfer
import DimensionFourDependence.IrreducibleHypersurfaceNoPlane

/-! # Finiteness of lines through a smooth point of a nonplanar image

Euler's identity puts the point in its tangent plane. Every contained
line through it lies there. The irreducible nonlinear equation cannot
vanish identically on that plane, so the checked planar slope calculation
gives a finite set of lines. The theorem applies to the actual image equation.
-/

namespace DimensionFourDependence

open MvPolynomial Module

variable {F : Type*} [Field F]

/-- A point of a homogeneous hypersurface belongs to its actual tangent kernel. -/
theorem homogeneous_point_mem_hypersurfaceTangentPlane
    (R : MvPolynomial (Fin 4) F) {d : ℕ} (hR : R.IsHomogeneous d)
    (O : Fin 4 → F) (hzero : aeval O R = 0) : O ∈ hypersurfaceTangentPlane R O := by
  have he := congrArg (aeval O) hR.sum_X_mul_pderiv
  simp only [map_sum, map_mul, aeval_X, map_nsmul, hzero, nsmul_zero] at he
  change (∑ i, aeval O (pderiv i R) * O i) = 0
  calc
    _ = ∑ i, O i * aeval O (pderiv i R) := by
      apply Finset.sum_congr rfl
      intro i _
      exact mul_comm _ _
    _ = 0 := he

variable [Infinite F]

/-- The tangent-plane argument and nonzero planar restriction imply
finiteness of all contained projective lines through the smooth point. -/
theorem homogeneous_hypersurface_finite_lines_at_smooth_point
    (R : MvPolynomial (Fin 4) F) {d : ℕ} (hR : R.IsHomogeneous d)
    (O : Fin 4 → F) (hO : O ≠ 0) (hzero : aeval O R = 0)
    (hsmooth : (fun i => aeval O (pderiv i R)) ≠ 0)
    (hnoPlane : ∀ T : Submodule F (Fin 4 → F), finrank F T = 3 → ¬ ∀ x ∈ T, aeval x R = 0) :
    {L : Submodule F (Fin 4 → F) | finrank F L = 2 ∧ O ∈ L ∧ (∀ x ∈ L, aeval x R = 0)}.Finite := by
  let T := hypersurfaceTangentPlane R O
  have hT : finrank F T = 3 := hypersurfaceTangentPlane_finrank R O hsmooth
  have hOT : O ∈ T := homogeneous_point_mem_hypersurfaceTangentPlane R hR O hzero
  have hfinite := finite_contained_lines_in_three_subspace R hR T hT O hOT hO (hnoPlane T hT)
  apply hfinite.subset
  intro L hL
  exact ⟨hL.1, contained_line_le_hypersurfaceTangentPlane R O L hL.2.1 hL.2.2, hL.2⟩

variable [CharZero F]

/-- Every smooth projective point of an irreducible homogeneous hypersurface
of degree at least two lies on only finitely many contained projective lines. -/
theorem irreducible_hypersurface_finite_lines_at_smooth_point
    (R : MvPolynomial (Fin 4) F) {d : ℕ} (hd : 2 ≤ d)
    (hR : R.IsHomogeneous d) (hirred : Irreducible R)
    (O : Fin 4 → F) (hO : O ≠ 0) (hzero : aeval O R = 0)
    (hsmooth : (fun i => aeval O (pderiv i R)) ≠ 0) :
    {L : Submodule F (Fin 4 → F) | finrank F L = 2 ∧ O ∈ L ∧ (∀ x ∈ L, aeval x R = 0)}.Finite := by
  exact homogeneous_hypersurface_finite_lines_at_smooth_point R hR O hO hzero hsmooth
    (fun T hT => irreducible_homogeneous_hypersurface_contains_no_plane R hd hR hirred T hT)

/-- Component independence makes the actual image equation nonlinear;
every smooth projective point of that equation lies on only finitely many lines. -/
theorem ImageRelationWitness.finite_lines_at_smooth_point
    (H : Fin 4 → MvPolynomial (Fin 4) F) {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d)
    (hind : ¬ ComponentsDependent H) (I : ImageRelationWitness H)
    (O : Fin 4 → F) (hO : O ≠ 0) (hzero : aeval O I.equation = 0)
    (hsmooth : (fun i => aeval O (pderiv i I.equation)) ≠ 0) :
    {L : Submodule F (Fin 4 → F) | finrank F L = 2 ∧ O ∈ L ∧
      (∀ x ∈ L, aeval x I.equation = 0)}.Finite := by
  have hdeg : 2 ≤ I.degree := by
    have hp := I.degree_pos
    by_contra hn
    have he : I.degree = 1 := by omega
    exact hind (I.dependent_of_degree_one H hd hH he)
  exact irreducible_hypersurface_finite_lines_at_smooth_point I.equation hdeg I.homogeneous
    I.irreducible O hO hzero hsmooth

end DimensionFourDependence
