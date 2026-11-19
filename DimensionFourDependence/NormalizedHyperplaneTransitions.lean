import DimensionFourDependence.ProjectiveNormalizedSection

/-! # Hyperplane frame transitions on the actual normalized overlaps

The coordinate ratio and its inverse are actual regular functions on the
original principal overlap. They construct a unit in its normalization.
Both original normalized charts restrict to that same overlap, retaining
their exact original rational values.
-/

namespace DimensionFourDependence

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 2000000

variable {k F : Type*} [Field k] [Field F] [Algebra k F]

/-- Integral closures restrict along an actual inclusion of coordinate
subalgebras, with their original field values. -/
noncomputable def integralClosureSubalgebraRestriction
    (A B : Subalgebra k F) (h : A ≤ B) : integralClosure A F →+* integralClosure B F := by
  let : Algebra A B := (Subalgebra.inclusion h).toAlgebra
  let : IsScalarTower A B F := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  exact
    { toFun := fun z => ⟨z.val, z.property.tower_top⟩
      map_zero' := rfl
      map_one' := rfl
      map_add' := fun _ _ => rfl
      map_mul' := fun _ _ => rfl }

/-- Every actual restriction retains the same original rational function. -/
theorem integralClosureSubalgebraRestriction_value
    (A B : Subalgebra k F) (h : A ≤ B) (z : integralClosure A F) :
    (integralClosureSubalgebraRestriction A B h z : F) = z := rfl

/-- The original chart algebra includes into its original principal overlap. -/
theorem projective_chart_algebra_le_overlap (x : Fin 4 → F) (i j : Fin 4) :
    projectiveCoordinateChartAlgebra (C := k) x i ≤ projectiveChartOverlap (C := k) x i j := by
  apply Algebra.adjoin_le
  rintro _ ⟨a, rfl⟩
  exact Algebra.subset_adjoin (Or.inl ⟨a, rfl⟩)

/-- The other original chart includes into the same original overlap. -/
theorem projective_other_chart_algebra_le_overlap (x : Fin 4 → F) (i j : Fin 4)
    (hi : x i ≠ 0) (hj : x j ≠ 0) :
    projectiveCoordinateChartAlgebra (C := k) x j ≤ projectiveChartOverlap (C := k) x i j := by
  rw [projectiveChartOverlapAlgebra_symm x i j hi hj]
  exact projective_chart_algebra_le_overlap x j i

/-- Restriction of a regular coefficient from the first original
normalized chart to its actual normalized principal overlap. -/
noncomputable def normalizedProjectiveOverlapLeft
    (x : Fin 4 → F) (i j : Fin 4) :
    integralClosure (projectiveCoordinateChartAlgebra (C := k) x i) F →+*
      integralClosure (projectiveChartOverlap (C := k) x i j) F :=
  integralClosureSubalgebraRestriction _ _ (projective_chart_algebra_le_overlap x i j)

/-- Restriction from the other original normalized chart to the same
actual normalized principal overlap. -/
noncomputable def normalizedProjectiveOverlapRight
    (x : Fin 4 → F) (i j : Fin 4) (hi : x i ≠ 0) (hj : x j ≠ 0) :
    integralClosure (projectiveCoordinateChartAlgebra (C := k) x j) F →+*
      integralClosure (projectiveChartOverlap (C := k) x i j) F :=
  integralClosureSubalgebraRestriction _ _ (projective_other_chart_algebra_le_overlap x i j hi hj)

/-- The actual hyperplane frame change is a regular unit on the
normalized original overlap, with the original reciprocal as inverse. -/
noncomputable def normalizedHyperplaneTransitionUnit
    (x : Fin 4 → F) (i j : Fin 4) (hi : x i ≠ 0) (hj : x j ≠ 0) :
    (integralClosure (projectiveChartOverlap (C := k) x i j) F)ˣ := by
  let R := projectiveChartOverlap (C := k) x i j
  let a : R := ⟨x j / x i, Algebra.subset_adjoin (Or.inl ⟨j, rfl⟩)⟩
  let b : R := ⟨x i / x j, Algebra.subset_adjoin (Or.inr rfl)⟩
  refine
    { val := algebraMap R (integralClosure R F) a
      inv := algebraMap R (integralClosure R F) b
      val_inv := ?_
      inv_val := ?_ }
  · apply Subtype.ext
    change x j / x i * (x i / x j) = 1
    field_simp
  · apply Subtype.ext
    change x i / x j * (x j / x i) = 1
    field_simp

/-- The constructed regular transition has exactly the original
coordinate-ratio value in the common function field. -/
theorem normalizedHyperplaneTransitionUnit_value
    (x : Fin 4 → F) (i j : Fin 4) (hi : x i ≠ 0) (hj : x j ≠ 0) :
    (((normalizedHyperplaneTransitionUnit (k := k) x i j hi hj :
      (integralClosure (projectiveChartOverlap (C := k) x i j) F)ˣ) :
      integralClosure (projectiveChartOverlap (C := k) x i j) F) : F) = x j / x i := rfl

/-- Equality of actual normalized-overlap frame coefficients is exactly
the original homogeneous hyperplane transition in the common field. -/
theorem normalized_hyperplane_overlap_transition_iff
    (x : Fin 4 → F) (i j : Fin 4) (hi : x i ≠ 0) (hj : x j ≠ 0)
    (a : integralClosure (projectiveCoordinateChartAlgebra (C := k) x i) F)
    (b : integralClosure (projectiveCoordinateChartAlgebra (C := k) x j) F) :
    normalizedProjectiveOverlapLeft x i j a =
      (normalizedHyperplaneTransitionUnit (k := k) x i j hi hj :
        integralClosure (projectiveChartOverlap (C := k) x i j) F) *
          normalizedProjectiveOverlapRight x i j hi hj b ↔
      (a : F) * x i = (b : F) * x j := by
  rw [Subtype.ext_iff]
  change (a : F) = (x j / x i) * (b : F) ↔ (a : F) * x i = (b : F) * x j
  constructor
  · intro h
    rw [h]
    field_simp
  · intro h
    apply (mul_right_cancel₀ hi)
    rw [h]
    field_simp

end DimensionFourDependence
