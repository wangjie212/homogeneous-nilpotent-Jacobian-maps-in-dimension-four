import DimensionFourDependence.CommonFiniteDirectionTangentField

/-! # Enlarging the actual finite tangent field by algebraic cone coefficients

The finite tangent field can be enlarged inside the same geometric
constants to contain any finite algebraic coefficient family. The entire
original field and every added actual coefficient remain in one finite
extension of the original ruling field.
-/

namespace DimensionFourDependence

variable {C E : Type*} [Field C] [Field E] [Algebra C E]

/-- A finite actual coefficient field and a finite family of actual
algebraic values construct a common finite intermediate extension. -/
theorem finite_intermediate_field_enlarge_by_algebraic_values
    (L : IntermediateField C E) (hL : Module.Finite C L)
    (s : Finset E) (hs : ∀ x ∈ s, IsAlgebraic C x) :
    ∃ F : IntermediateField C E, Module.Finite C F ∧ L ≤ F ∧ (s : Set E) ⊆ F := by
  let : Module.Finite C L := hL
  let F' := IntermediateField.adjoin L (s : Set E)
  have hfiniteL : Module.Finite L F' := by
    apply IntermediateField.finiteDimensional_adjoin
    intro x hx
    exact ((hs x hx).tower_top L).isIntegral
  let : Module.Finite L F' := hfiniteL
  have hfiniteC : Module.Finite C F' := Module.Finite.trans (R := C) L F'
  let F := F'.restrictScalars C
  refine ⟨F, hfiniteC, ?_, ?_⟩
  · intro x hx
    exact F'.algebraMap_mem ⟨x, hx⟩
  · intro x hx
    exact IntermediateField.subset_adjoin L _ hx

end DimensionFourDependence
