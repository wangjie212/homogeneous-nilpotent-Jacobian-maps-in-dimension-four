import DimensionFourDependence.NormalizedHyperplaneTransitions

/-! # The original hyperplane transition units satisfy the actual triple-overlap cocycle -/

namespace DimensionFourDependence

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 2000000

variable {k F : Type*} [Field k] [Field F] [Algebra k F]

/-- The original triple overlap inside the same actual function field. -/
noncomputable def projectiveTripleOverlap (x : Fin 4 → F) (i j l : Fin 4) : Subalgebra k F :=
  Algebra.adjoin k (Set.range (fun a => x a / x i) ∪ {x i / x j, x i / x l})

/-- The first double overlap includes into the original triple overlap. -/
theorem projective_overlap_le_triple_left (x : Fin 4 → F) (i j l : Fin 4) :
    projectiveChartOverlap (C := k) x i j ≤ projectiveTripleOverlap (k := k) x i j l := by
  apply Algebra.adjoin_le
  intro z hz
  rcases hz with ⟨a, rfl⟩ | rfl
  · exact Algebra.subset_adjoin (Or.inl ⟨a, rfl⟩)
  · exact Algebra.subset_adjoin (Or.inr (Set.mem_insert _ _))

/-- The outside double overlap includes into that same triple overlap. -/
theorem projective_overlap_le_triple_outer (x : Fin 4 → F) (i j l : Fin 4) :
    projectiveChartOverlap (C := k) x i l ≤ projectiveTripleOverlap (k := k) x i j l := by
  apply Algebra.adjoin_le
  intro z hz
  rcases hz with ⟨a, rfl⟩ | rfl
  · exact Algebra.subset_adjoin (Or.inl ⟨a, rfl⟩)
  · exact Algebra.subset_adjoin (Or.inr (Set.mem_insert_of_mem _ (Set.mem_singleton _)))

/-- The remaining double overlap includes into that same triple
overlap, through its original rational coordinate functions. -/
theorem projective_overlap_le_triple_right (x : Fin 4 → F) (i j l : Fin 4)
    (hi : x i ≠ 0) (hj : x j ≠ 0) :
    projectiveChartOverlap (C := k) x j l ≤ projectiveTripleOverlap (k := k) x i j l := by
  let R := projectiveTripleOverlap (k := k) x i j l
  have hrat (a : Fin 4) : x a / x i ∈ R := Algebra.subset_adjoin (Or.inl ⟨a, rfl⟩)
  have hij : x i / x j ∈ R := Algebra.subset_adjoin (Or.inr (Set.mem_insert _ _))
  have hil : x i / x l ∈ R :=
    Algebra.subset_adjoin (Or.inr (Set.mem_insert_of_mem _ (Set.mem_singleton _)))
  apply Algebra.adjoin_le
  intro z hz
  rcases hz with ⟨a, rfl⟩ | rfl
  · have hvalue : x a / x j = (x a / x i) * (x i / x j) := by field_simp
    change x a / x j ∈ R
    rw [hvalue]
    exact R.mul_mem (hrat a) hij
  · have hvalue : x j / x l = (x j / x i) * (x i / x l) := by field_simp
    rw [hvalue]
    exact R.mul_mem (hrat j) hil

/-- In the actual normalized triple-overlap ring, the original
hyperplane transition units satisfy the line-bundle cocycle identity. -/
theorem normalized_hyperplane_transition_cocycle
    (x : Fin 4 → F) (i j l : Fin 4)
    (hi : x i ≠ 0) (hj : x j ≠ 0) (hl : x l ≠ 0) :
    let R := projectiveTripleOverlap (k := k) x i j l
    let f := integralClosureSubalgebraRestriction _ R (projective_overlap_le_triple_left x i j l)
    let g := integralClosureSubalgebraRestriction _ R (projective_overlap_le_triple_right x i j l hi hj)
    let h := integralClosureSubalgebraRestriction _ R (projective_overlap_le_triple_outer x i j l)
    (normalizedHyperplaneTransitionUnit (k := k) x i j hi hj).map f.toMonoidHom *
      (normalizedHyperplaneTransitionUnit (k := k) x j l hj hl).map g.toMonoidHom =
        (normalizedHyperplaneTransitionUnit (k := k) x i l hi hl).map h.toMonoidHom := by
  apply Units.ext
  apply Subtype.ext
  change (x j / x i) * (x l / x j) = x l / x i
  field_simp

end DimensionFourDependence
