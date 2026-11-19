import DimensionFourDependence.FiniteTangentProportionality

/-! # The constructed tangent proportionality field is finite over the ruling field

If the direction coefficients already lie in a finite extension of the
actual ruling field, adjoining the actual tangent ratio remains finite
over that original ruling field. The scalar is kept in this same field.
-/

namespace DimensionFourDependence

variable {L F E : Type*} [Field L] [Field F] [Field E]
    [Algebra L F] [Algebra F E] [Algebra L E] [IsScalarTower L F E] [Module.Finite L F]

/-- The same actual adjoin field and actual proportionality scalar
are finite and algebraic over the original ruling field. -/
theorem finite_direction_extension_constructs_ruling_finite_tangent_field
    (T r : E) (hT : T ≠ 0) (hr : r ≠ 0) (halg : IsAlgebraic F (r / T)) :
    IsAlgebraic L (r / T) ∧
      Module.Finite L (IntermediateField.adjoin F {r / T}) ∧
      ∃ u : IntermediateField.adjoin F {r / T}, u ≠ 0 ∧ r = (u : E) * T := by
  obtain ⟨hfinite, u, hu, he⟩ := algebraic_tangent_ratio_constructs_finite_proportionality T r hT hr halg
  let : Module.Finite F (IntermediateField.adjoin F {r / T}) := hfinite
  have hfiniteL : Module.Finite L (IntermediateField.adjoin F {r / T}) :=
    Module.Finite.trans (R := L) F _
  have halgL : IsAlgebraic L (r / T) := halg.restrictScalars L
  exact ⟨halgL, hfiniteL, u, hu, he⟩

end DimensionFourDependence
