import DimensionFourDependence.ProjectionGeneratorOriginalField

/-! # The original projection fiber generates the field after base reindexing -/

namespace DimensionFourDependence

universe u

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000

variable {k K L : Type u} [Field k] [Field K] [Field L]
  [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L]

/-- Reindexing the actual three projection coordinates leaves the
single fiber generator and entire original function field unchanged. -/
theorem projection_fiber_generator_of_reindexed_original_coordinates
    (T : (Fin 3 → k) ≃ₗ[k] (Fin 3 → k)) (x : Fin 3 → L)
    (hx : IntermediateField.adjoin k (Set.range x) = ⊤)
    (r : Fin 3 ≃ Fin 3) (v : L) (b : Fin 2 → K)
    (hcoordinates : (fun i => linearProjectionCoordinate T x (r i)) =
      ![v, algebraMap K L (b 0), algebraMap K L (b 1)]) :
    IntermediateField.adjoin K {v} = ⊤ := by
  have hgen := linearProjectionCoordinate_field_adjoin_eq_top T x hx
  let U := IntermediateField.adjoin K {v}
  have hle : IntermediateField.adjoin k (Set.range (linearProjectionCoordinate T x)) ≤
      U.restrictScalars k := by
    apply IntermediateField.adjoin_le_iff.mpr
    rintro _ ⟨j, rfl⟩
    obtain ⟨i, rfl⟩ := r.surjective j
    rw [congrFun hcoordinates i]
    fin_cases i
    · exact IntermediateField.subset_adjoin K _ (Set.mem_singleton v)
    · exact U.algebraMap_mem (b 0)
    · exact U.algebraMap_mem (b 1)
  apply IntermediateField.restrictScalars_injective k
  rw [IntermediateField.restrictScalars_top]
  apply top_unique
  rw [← hgen]
  exact hle

end DimensionFourDependence
