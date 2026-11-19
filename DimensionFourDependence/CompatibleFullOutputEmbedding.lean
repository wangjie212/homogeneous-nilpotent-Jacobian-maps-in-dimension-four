import DimensionFourDependence.GenericOutputPoint

/-! # Original source and target embeddings construct the full output-field embedding -/

namespace DimensionFourDependence

set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {K S C G : Type*} [Field K] [Field S] [Field C] [Field G]
  [Algebra K S] [Algebra K C] [Algebra K G] {n : ℕ}

/-- Exact original component values put every element of the full
original output field in the given coefficient-field image. -/
theorem compatible_full_output_field_maps_into_coefficient_image
    (Φ : S →ₐ[K] G) (Γ : C →ₐ[K] G) (H : Fin n → S) (Y : Fin n → C)
    (hY : ∀ i, Φ (H i) = Γ (Y i)) (a : fullOutputField (K := K) H) :
    Φ (a : S) ∈ Γ.fieldRange := by
  have hle : fullOutputField (K := K) H ≤ Γ.fieldRange.comap Φ := by
    apply IntermediateField.adjoin_le_iff.mpr
    rintro _ ⟨i, rfl⟩
    exact ⟨Y i, (hY i).symm⟩
  exact hle a.property

/-- The actual full output field embeds in the specified coefficient
field by the given common source realization, not by an unrelated
isomorphism of abstract output fields. -/
noncomputable def compatibleFullOutputFieldHom
    (Φ : S →ₐ[K] G) (Γ : C →ₐ[K] G) (H : Fin n → S) (Y : Fin n → C)
    (hY : ∀ i, Φ (H i) = Γ (Y i)) : fullOutputField (K := K) H →ₐ[K] C :=
  Γ.equivFieldRange.symm.toAlgHom.comp
    ((Φ.comp (fullOutputField (K := K) H).val).codRestrict Γ.fieldRange.toSubalgebra
      (fun a => compatible_full_output_field_maps_into_coefficient_image Φ Γ H Y hY a))

/-- The constructed full output embedding commutes with the entire
original source-field realization, on every output-field element. -/
theorem compatibleFullOutputFieldHom_source_value
    (Φ : S →ₐ[K] G) (Γ : C →ₐ[K] G) (H : Fin n → S) (Y : Fin n → C)
    (hY : ∀ i, Φ (H i) = Γ (Y i)) (a : fullOutputField (K := K) H) :
    Γ (compatibleFullOutputFieldHom Φ Γ H Y hY a) = Φ (a : S) := by
  exact congrArg (fun z : Γ.fieldRange => (z : G)) (Γ.equivFieldRange.apply_symm_apply
    ⟨Φ (a : S), compatible_full_output_field_maps_into_coefficient_image Φ Γ H Y hY a⟩)

/-- Every original output coordinate becomes exactly its prescribed
generic target coordinate under that same full-field embedding. -/
theorem compatibleFullOutputFieldHom_coordinate
    (Φ : S →ₐ[K] G) (Γ : C →ₐ[K] G) (H : Fin n → S) (Y : Fin n → C)
    (hY : ∀ i, Φ (H i) = Γ (Y i)) (i : Fin n) :
    compatibleFullOutputFieldHom Φ Γ H Y hY (fullOutputCoordinate (K := K) H i) = Y i := by
  apply Γ.injective
  exact (compatibleFullOutputFieldHom_source_value Φ Γ H Y hY _).trans (hY i)

end DimensionFourDependence
