import DimensionFourDependence.ProjectiveChartOverlaps

/-! # The three free ratios generate each original four-coordinate projective chart -/

namespace DimensionFourDependence

variable {C F : Type*} [Field C] [Field F] [Algebra C F]

/-- Dropping the selected coordinate, which equals one in its own
frame, retains the entire original projective coordinate algebra. -/
theorem projectiveCoordinateChartAlgebra_eq_three_ratios
    (x : Fin 4 → F) (s : Fin 4 ≃ Option (Fin 3)) (hx : x (s.symm none) ≠ 0) :
    projectiveCoordinateChartAlgebra (C := C) x (s.symm none) =
      Algebra.adjoin C (Set.range (fun j : Fin 3 => x (s.symm (some j)) / x (s.symm none))) := by
  apply le_antisymm
  · apply Algebra.adjoin_le
    rintro _ ⟨i, rfl⟩
    change x i / x (s.symm none) ∈ _
    rcases hsi : s i with _ | j
    · have hi : i = s.symm none := by rw [← hsi, s.symm_apply_apply]
      rw [hi, div_self hx]
      exact Subalgebra.one_mem _
    · have hi : i = s.symm (some j) := by rw [← hsi, s.symm_apply_apply]
      rw [hi]
      exact Algebra.subset_adjoin ⟨j, rfl⟩
  · apply Algebra.adjoin_le
    rintro _ ⟨j, rfl⟩
    exact projectiveCoordinateChartAlgebra_ratio_mem (C := C) x (s.symm none) (s.symm (some j))

end DimensionFourDependence
