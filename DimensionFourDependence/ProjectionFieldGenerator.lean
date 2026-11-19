import DimensionFourDependence.Defs

/-! # A three-coordinate field has one fiber generator over its projection field -/

namespace DimensionFourDependence

variable {k K L : Type*} [Field k] [Field K] [Field L]
  [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L]

/-- If two of three generating coordinates are already in the actual
projection field, the remaining coordinate generates the fiber extension. -/
theorem projection_field_generator_of_three_coordinates
    (u z v : L) (hgen : IntermediateField.adjoin k {u, z, v} = ⊤)
    (hu : ∃ a : K, algebraMap K L a = u)
    (hz : ∃ a : K, algebraMap K L a = z) :
    IntermediateField.adjoin K {v} = ⊤ := by
  apply IntermediateField.restrictScalars_injective k
  rw [IntermediateField.restrictScalars_top]
  apply top_unique
  rw [← hgen]
  apply IntermediateField.adjoin_le_iff.mpr
  intro x hx
  rcases hx with rfl | rfl | rfl
  · obtain ⟨a, rfl⟩ := hu
    exact (IntermediateField.adjoin K {v}).algebraMap_mem a
  · obtain ⟨a, rfl⟩ := hz
    exact (IntermediateField.adjoin K {v}).algebraMap_mem a
  · exact IntermediateField.subset_adjoin K _ (by simp)

end DimensionFourDependence
