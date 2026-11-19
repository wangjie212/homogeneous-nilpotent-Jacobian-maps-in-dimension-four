import DimensionFourDependence.AdjoinInverseLocalization
import DimensionFourDependence.ClosedGaussPencilCharts

/-! # Actual overlap localizations of the projective source charts

All chart and overlap rings are realized inside the same source field.
Changing the nonzero homogeneous coordinate gives equal overlap subalgebras,
and the corresponding maps are the actual identity on source functions.
-/

namespace DimensionFourDependence

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 200000

variable {C F : Type*} [Field C] [Field F] [Algebra C F]

/-- A projective coordinate chart, using all four ratios including the
ratio equal to one at its chosen coordinate. -/
noncomputable def projectiveCoordinateChartAlgebra (x : Fin 4 → F) (a : Fin 4) : Subalgebra C F :=
  Algebra.adjoin C (Set.range (fun i => x i / x a))

/-- Every original coordinate ratio belongs to the actual chart. -/
theorem projectiveCoordinateChartAlgebra_ratio_mem (x : Fin 4 → F) (a i : Fin 4) :
    x i / x a ∈ projectiveCoordinateChartAlgebra (C := C) x a :=
  Algebra.subset_adjoin ⟨i, rfl⟩

/-- The actual transition denominator between two projective charts. -/
noncomputable def projectiveChartTransition (x : Fin 4 → F) (a b : Fin 4) :
    projectiveCoordinateChartAlgebra (C := C) x a :=
  ⟨x b / x a, projectiveCoordinateChartAlgebra_ratio_mem x a b⟩

/-- The overlap obtained by adjoining the actual inverse transition ratio. -/
noncomputable def projectiveChartOverlapAlgebra (x : Fin 4 → F) (a b : Fin 4) :
    Subalgebra (projectiveCoordinateChartAlgebra (C := C) x a) F :=
  adjoinInverseAlgebra (F := F) (projectiveChartTransition (C := C) x a b)

/-- The overlap as an algebra over the original coefficient field. -/
noncomputable def projectiveChartOverlap (x : Fin 4 → F) (a b : Fin 4) : Subalgebra C F :=
  Algebra.adjoin C (Set.range (fun i => x i / x a) ∪ {x a / x b})

/-- The actual overlap is the principal localization of its source chart. -/
theorem projectiveChartOverlapAlgebra_isLocalization (x : Fin 4 → F) (a b : Fin 4)
    (ha : x a ≠ 0) (hb : x b ≠ 0) :
    IsLocalization.Away (projectiveChartTransition (C := C) x a b)
      (projectiveChartOverlapAlgebra (C := C) x a b) :=
  adjoinInverseAlgebra_isLocalization _ (div_ne_zero hb ha)

/-- The overlap's original coefficient algebra consists of the original
chart ratios and the inverse transition ratio. -/
theorem projectiveChartOverlapAlgebra_restrictScalars (x : Fin 4 → F) (a b : Fin 4) :
    (projectiveChartOverlapAlgebra (C := C) x a b).restrictScalars C =
      Algebra.adjoin C (Set.range (fun i => x i / x a) ∪ {x a / x b}) := by
  change (Algebra.adjoin (Algebra.adjoin C (Set.range (fun i => x i / x a)))
    {(x b / x a)⁻¹}).restrictScalars C = _
  rw [inv_div, ← Algebra.adjoin_union_eq_adjoin_adjoin]

/-- Either projective coordinate gives exactly the same actual overlap
subalgebra in the original source field. -/
theorem projectiveChartOverlapAlgebra_symm (x : Fin 4 → F) (a b : Fin 4)
    (ha : x a ≠ 0) (hb : x b ≠ 0) :
    projectiveChartOverlap (C := C) x a b = projectiveChartOverlap (C := C) x b a := by
  have half (a b : Fin 4) (ha : x a ≠ 0) (hb : x b ≠ 0) :
      Algebra.adjoin C (Set.range (fun i => x i / x a) ∪ {x a / x b}) ≤
        Algebra.adjoin C (Set.range (fun i => x i / x b) ∪ {x b / x a}) := by
    apply Algebra.adjoin_le
    intro y hy
    rcases hy with ⟨i, rfl⟩ | rfl
    · have hi : x i / x b ∈ Algebra.adjoin C
          (Set.range (fun i => x i / x b) ∪ {x b / x a}) := Algebra.subset_adjoin (Or.inl ⟨i, rfl⟩)
      have hba : x b / x a ∈ Algebra.adjoin C
          (Set.range (fun i => x i / x b) ∪ {x b / x a}) := Algebra.subset_adjoin (Or.inr rfl)
      have he : x i / x a = (x i / x b) * (x b / x a) := by field_simp
      dsimp only
      rw [he]
      exact Subalgebra.mul_mem _ hi hba
    · exact Algebra.subset_adjoin (Or.inl ⟨a, rfl⟩)
  exact le_antisymm (half a b ha hb) (half b a hb ha)

/-- The transition between overlap coordinate rings is the identity on
the actual original-source rational functions. -/
noncomputable def projectiveChartOverlapEquiv (x : Fin 4 → F) (a b : Fin 4)
    (ha : x a ≠ 0) (hb : x b ≠ 0) :
    projectiveChartOverlap (C := C) x a b ≃ₐ[C] projectiveChartOverlap (C := C) x b a :=
  Subalgebra.equivOfEq _ _ (projectiveChartOverlapAlgebra_symm (C := C) x a b ha hb)

theorem projectiveChartOverlapEquiv_coe (x : Fin 4 → F) (a b : Fin 4)
    (ha : x a ≠ 0) (hb : x b ≠ 0)
    (z : projectiveChartOverlap (C := C) x a b) :
    ((projectiveChartOverlapEquiv (C := C) x a b ha hb z :
      projectiveChartOverlap (C := C) x b a) : F) = z := by
  simp only [projectiveChartOverlapEquiv, Subalgebra.equivOfEq_apply]

end DimensionFourDependence
