import DimensionFourDependence.PlanarLineFiniteness
import DimensionFourDependence.PointAdaptedCoordinates
import DimensionFourDependence.LinearPolynomialCoordinates

/-! # Finiteness of contained lines in an arbitrary three-dimensional plane

Point-adapted linear coordinates transfer the explicit slope calculation
to a three-dimensional vector subspace of four-coordinate space. A
nonzero restriction of the homogeneous equation gives finiteness there.
-/

namespace DimensionFourDependence

open MvPolynomial Matrix Module

variable {F A : Type*} [Field F] [Infinite F] [AddCommGroup A] [Module F A]

/-- Transport the finite planar line set along a linear coordinate isomorphism. -/
theorem finite_contained_lines_in_point_coordinates
    (e : A ≃ₗ[F] (Fin 3 → F)) (O : A) (heO : e O = ![1, 0, 0])
    (R : MvPolynomial (Fin 3) F) {d : ℕ} (hR : R.IsHomogeneous d) (hR0 : R ≠ 0) :
    {L : Submodule F A | finrank F L = 2 ∧ O ∈ L ∧
      (∀ x ∈ L, aeval (e x) R = 0)}.Finite := by
  have hs := homogeneous_plane_finite_lines_through_first_point R hR hR0
  apply (hs.image (fun M : Submodule F (Fin 3 → F) => M.map e.symm.toLinearMap)).subset
  intro L hL
  let M := L.map e.toLinearMap
  refine ⟨M, ?_, ?_⟩
  · change finrank F M = 2 ∧ (![1, 0, 0] : Fin 3 → F) ∈ M ∧
      (∀ x ∈ M, aeval x R = 0)
    refine ⟨(e.finrank_map_eq L).trans hL.1, ⟨O, hL.2.1, heO⟩, ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    exact hL.2.2 x hx
  · change (L.map e.toLinearMap).map e.symm.toLinearMap = L
    have hc : e.symm.toLinearMap.comp e.toLinearMap = LinearMap.id := by
      ext x
      exact e.symm_apply_apply x
    rw [← Submodule.map_comp, hc, Submodule.map_id]

omit [AddCommGroup A] [Module F A] in
/-- If a three-dimensional plane is not contained in the homogeneous
hypersurface, only finitely many contained lines in that plane pass through
a fixed nonzero point of the plane. -/
theorem finite_contained_lines_in_three_subspace
    (R : MvPolynomial (Fin 4) F) {d : ℕ} (hR : R.IsHomogeneous d)
    (T : Submodule F (Fin 4 → F)) (hT : finrank F T = 3)
    (O : Fin 4 → F) (hO : O ∈ T) (hO0 : O ≠ 0)
    (hnot : ¬ ∀ x ∈ T, aeval x R = 0) :
    {L : Submodule F (Fin 4 → F) | finrank F L = 2 ∧ L ≤ T ∧
      O ∈ L ∧ (∀ x ∈ L, aeval x R = 0)}.Finite := by
  let o : T := ⟨O, hO⟩
  have ho : o ≠ 0 := fun hz => hO0 (congrArg Subtype.val hz)
  obtain ⟨e, heO⟩ := three_space_coordinates_with_point hT o ho
  let f := T.subtype.comp e.symm.toLinearMap
  let P := linearPolynomialPullback (LinearMap.toMatrix' f) R
  have heval (x : T) : aeval (e x) P = aeval (x : Fin 4 → F) R := by
    rw [linearPolynomialPullback_toMatrix_aeval]
    change aeval (T.subtype (e.symm (e x))) R = _
    rw [e.symm_apply_apply]
    rfl
  have hP : P.IsHomogeneous d := linearPolynomialPullback_homogeneous _ R hR
  have hP0 : P ≠ 0 := by
    intro hz
    apply hnot
    intro x hx
    have he := heval ⟨x, hx⟩
    rw [hz, map_zero] at he
    exact he.symm
  have hs := finite_contained_lines_in_point_coordinates e o heO P hP hP0
  apply (hs.image (fun M : Submodule F T => M.map T.subtype)).subset
  intro L hL
  let M := L.comap T.subtype
  refine ⟨M, ?_, ?_⟩
  · change finrank F M = 2 ∧ o ∈ M ∧ (∀ x ∈ M, aeval (e x) P = 0)
    refine ⟨(Submodule.comapSubtypeEquivOfLe hL.2.1).finrank_eq.trans hL.1, hL.2.2.1, ?_⟩
    intro x hx
    rw [heval]
    exact hL.2.2.2 x hx
  · change (L.comap T.subtype).map T.subtype = L
    rw [Submodule.map_comap_subtype, inf_eq_right.mpr hL.2.1]

end DimensionFourDependence
