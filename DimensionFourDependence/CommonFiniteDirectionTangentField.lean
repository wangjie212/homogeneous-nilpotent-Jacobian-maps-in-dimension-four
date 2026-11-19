import DimensionFourDependence.RulingFiniteTangentField

/-! # One actual finite field contains the direction and tangent multiplier

Adjoining the actual direction coordinates and the actual tangent ratio
constructs one finite extension of the ruling field. It retains every
coordinate and the nonzero scalar in the same ambient field.
-/

namespace DimensionFourDependence

variable {L E : Type*} [Field L] [Field E] [Algebra L E] {n : ℕ}

/-- Algebraicity constructs one actual finite intermediate field
containing all original directions and the nonzero tangent multiplier. -/
theorem algebraic_direction_and_tangent_ratio_construct_common_finite_field
    (A : Fin n → E) (hA : ∀ i, IsAlgebraic L (A i))
    (T r : E) (hT : T ≠ 0) (hr : r ≠ 0) (halg : IsAlgebraic L (r / T)) :
    ∃ D : IntermediateField L E, Module.Finite L D ∧ (∀ i, A i ∈ D) ∧
      ∃ u : D, u ≠ 0 ∧ r = (u : E) * T := by
  let S : Set E := Set.range A ∪ {r / T}
  let D := IntermediateField.adjoin L S
  have hfinite : Module.Finite L D := by
    apply IntermediateField.finiteDimensional_adjoin
    rintro z (⟨i, rfl⟩ | rfl)
    · exact (hA i).isIntegral
    · exact halg.isIntegral
  have hmem : r / T ∈ D := IntermediateField.subset_adjoin L _ (Or.inr rfl)
  let u : D := ⟨r / T, hmem⟩
  refine ⟨D, hfinite, (fun i => IntermediateField.subset_adjoin L _ (Or.inl ⟨i, rfl⟩)), u, ?_, ?_⟩
  · intro hz
    have he := congrArg (fun v : D => (v : E)) hz
    exact div_ne_zero hr hT he
  · exact (div_mul_cancel₀ r hT).symm

end DimensionFourDependence
