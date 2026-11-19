import DimensionFourDependence.SpecifiedRulingDualCoordinates
import DimensionFourDependence.GraphBoundaryProportionality
import DimensionFourDependence.VertexParabolaFromInfinity

/-! # Reconstruct the full fixed direction from its graph coordinates -/

namespace DimensionFourDependence

open Matrix Module MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra

set_option maxHeartbeats 1000000

variable {F : Type*} [Field F]

/-- A nonzero ternary normal has a two-dimensional ruling kernel. -/
theorem nonzero_ternary_normal_kernel_finrank (normal : Fin 3 → F) (hn : normal ≠ 0) :
    finrank F (LinearMap.ker (dotProductBilin F F normal)) = 2 := by
  classical
  obtain ⟨i, hi⟩ : ∃ i, normal i ≠ 0 := by
    simpa only [ne_eq, funext_iff, Pi.zero_apply, not_forall] using hn
  let T := dotProductBilin F F normal
  have hsurj : Function.Surjective T := by
    intro x
    refine ⟨Pi.single i (x / normal i), ?_⟩
    change normal ⬝ᵥ Pi.single i (x / normal i) = x
    rw [dotProduct_single]
    field_simp
  have he := LinearMap.finrank_range_add_finrank_ker T
  rw [LinearMap.range_eq_top.mpr hsurj] at he
  simp only [finrank_top, finrank_self, Module.finrank_pi, Fintype.card_fin] at he
  change finrank F (LinearMap.ker T) = 2
  omega

/-- The graph equation reconstructs the entire original vector. -/
theorem graphBoundaryDirection_eq_full_vector
    (p : Equiv.Perm (Fin 4)) (A : Fin 3 → F) (v : Fin 4 → F)
    (hlinear : v (p 3) = A ⬝ᵥ (fun i : Fin 3 => v (p i.castSucc))) :
    graphBoundaryDirection p A (fun i : Fin 3 => v (p i.castSucc)) = v := by
  funext j
  obtain ⟨i, rfl⟩ := p.surjective j
  refine Fin.lastCases ?_ (fun i => ?_) i
  · change graphBoundaryDirection p A (fun i : Fin 3 => v (p i.castSucc)) (p 3) = v (p 3)
    exact (graphBoundaryDirection_last p A _).trans hlinear.symm
  · exact graphBoundaryDirection_first p A _ i

variable {L S R : Type*} [Field L] [Field S] [Field R] [Algebra L S] [Algebra L R]

/-- An actual boundary proportional to the mapped fourth axis is
membership of the original rational fourth-axis point itself. -/
theorem actual_boundary_multiple_fourth_axis_gives_original_vertex_membership
    (x : Fin 4 → S) (z : Option (Fin 4) → R) (hz : z ≠ 0)
    (hpoint : projectiveFieldPoint (E := L) z hz ∈ projectiveClosureSet (L := L) x)
    (hz0 : z none = 0) (t : R) (ht : t ≠ 0)
    (hrep : (fun i => z (some i)) = t •
      (fun i => algebraMap L R ((Fin.snoc (0 : Fin 3 → L) 1 : Fin 4 → L) i))) :
    fourthAxisAffineInfinityPoint L ∈ projectiveClosureSet (L := L) x := by
  let axis : Fin 4 → L := Fin.snoc (0 : Fin 3 → L) 1
  let v : Fin 4 → R := fun i => z (some i)
  have ha : axis ≠ 0 := by
    intro hzero
    have he := congrFun hzero (Fin.last 3)
    exact one_ne_zero (by simpa only [axis, Fin.snoc_last, Pi.zero_apply] using he)
  have hv : v ≠ 0 := by
    intro hzero
    apply hz
    funext j
    cases j with
    | none => exact hz0
    | some i => exact congrFun hzero i
  have hzv : z = fun j : Option (Fin 4) => j.elim 0 v := by
    funext j
    cases j with
    | none => exact hz0
    | some i => rfl
  have hpoint' : projectiveFieldPoint (E := L) (fun j : Option (Fin 4) => j.elim 0 v)
      (by intro h; exact hv (funext (fun i => congrFun h (some i)))) ∈
        projectiveClosureSet (L := L) x := by
    simpa only [hzv] using hpoint
  have he := projective_infinity_point_eq_of_mapped_direction_multiple axis v ha hv t ht hrep
  rw [he, projectiveFieldPoint_self_eq_coordinatePoint] at hpoint'
  exact hpoint'

end DimensionFourDependence
