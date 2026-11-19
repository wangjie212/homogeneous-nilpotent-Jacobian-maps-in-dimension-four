import DimensionFourDependence.ProjectiveNormalizedPrimeCoordinates

/-! # Graph-boundary proportionality identifies the full original projective point

The original first invariant determines the fourth direction coordinate
from the first three. Proportional projected directions therefore give
proportional full original-coordinate directions, with the same scalar.
The resulting extension-valued infinity point equals the original
coefficient-field point represented by the fixed graph direction.
-/

namespace DimensionFourDependence

open Matrix MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra

variable {F R : Type*} [Field F] [Field R]

/-- The full original-coordinate boundary direction determined by
the three graph coordinates and their original linear graph equation. -/
noncomputable def graphBoundaryDirection (p : Equiv.Perm (Fin 4)) (A b : Fin 3 → F) : Fin 4 → F :=
  fun j => (Fin.snoc b (A ⬝ᵥ b) : Fin 4 → F) (p.symm j)

/-- The first three original graph coordinates retain their original values. -/
theorem graphBoundaryDirection_first
    (p : Equiv.Perm (Fin 4)) (A b : Fin 3 → F) (i : Fin 3) :
    graphBoundaryDirection p A b (p i.castSucc) = b i := by
  simp [graphBoundaryDirection]

/-- The fourth original graph coordinate is the specified linear pairing. -/
theorem graphBoundaryDirection_last
    (p : Equiv.Perm (Fin 4)) (A b : Fin 3 → F) :
    graphBoundaryDirection p A b (p 3) = A ⬝ᵥ b := by
  simp only [graphBoundaryDirection, Equiv.symm_apply_apply]
  exact @Fin.snoc_last 3 (fun _ => F) (A ⬝ᵥ b) b

/-- A nonzero projected direction constructs a nonzero full graph direction. -/
theorem graphBoundaryDirection_ne_zero
    (p : Equiv.Perm (Fin 4)) (A b : Fin 3 → F) (hb : b ≠ 0) :
    graphBoundaryDirection p A b ≠ 0 := by
  intro hzero
  apply hb
  funext i
  have he := congrFun hzero (p i.castSucc)
  simpa only [graphBoundaryDirection_first, Pi.zero_apply] using he

/-- Proportional first-three coordinates and the original fourth
coordinate graph equation imply full original-coordinate proportionality. -/
theorem graph_boundary_direction_proportional_of_first_coordinates
    (p : Equiv.Perm (Fin 4)) (A b : Fin 3 → F) (g : F →+* R)
    (v : Fin 4 → R) (t : R)
    (hlinear : v (p 3) = (fun i => g (A i)) ⬝ᵥ (fun i : Fin 3 => v (p i.castSucc)))
    (hfirst : (fun i : Fin 3 => v (p i.castSucc)) = t • (fun i => g (b i))) :
    v = t • (fun j => g (graphBoundaryDirection p A b j)) := by
  funext j
  obtain ⟨i, rfl⟩ := p.surjective j
  refine Fin.lastCases ?_ (fun i => ?_) i
  · change v (p 3) = t * g (graphBoundaryDirection p A b (p 3))
    rw [graphBoundaryDirection_last, hlinear, hfirst]
    simp only [dotProduct, Pi.smul_apply, smul_eq_mul, map_sum, map_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  · change v (p i.castSucc) = t * g (graphBoundaryDirection p A b (p i.castSucc))
    rw [graphBoundaryDirection_first]
    exact congrFun hfirst i

variable [Algebra F R]

/-- Nonzero proportional extension-valued infinity directions
represent the same actual point as the original rational direction. -/
theorem projective_infinity_point_eq_of_mapped_direction_multiple
    {sigma : Type*} (b : sigma → F) (v : sigma → R) (hb : b ≠ 0) (hv : v ≠ 0)
    (t : R) (ht : t ≠ 0) (hrep : v = t • (fun i => algebraMap F R (b i))) :
    projectiveFieldPoint (E := F) (fun j : Option sigma => j.elim 0 v)
      (by
        intro hzero
        apply hv
        funext i
        exact congrFun hzero (some i)) =
      projectiveFieldPoint (E := F) (fun j : Option sigma => j.elim 0 b)
        (by
          intro hzero
          apply hb
          funext i
          exact congrFun hzero (some i)) := by
  let B := fun j : Option sigma => j.elim 0 b
  have hB : B ≠ 0 := by
    intro hzero
    apply hb
    funext i
    exact congrFun hzero (some i)
  have hV : (fun j : Option sigma => j.elim 0 v) ≠ 0 := by
    intro hzero
    apply hv
    funext i
    exact congrFun hzero (some i)
  have he := projectiveFieldPoint_eq_of_proportional (K := F)
    (fun j : Option sigma => j.elim 0 v) (fun j => (Algebra.ofId F R) (B j)) hV
    (projective_coordinate_map_ne_zero (Algebra.ofId F R) B hB) t ht (by
      intro j
      cases j with
      | none => simp [B]
      | some i => exact congrFun hrep i)
  exact he.trans (projectiveFieldPoint_map_algHom (Algebra.ofId F R) B hB)

end DimensionFourDependence
