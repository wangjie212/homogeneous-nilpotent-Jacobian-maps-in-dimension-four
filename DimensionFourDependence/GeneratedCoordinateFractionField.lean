import DimensionFourDependence.Defs

/-! # The original algebra coordinates generate its whole fraction field -/

namespace DimensionFourDependence

variable {k A L σ : Type*} [Field k] [CommRing A] [Algebra k A]
  [Field L] [Algebra A L] [IsFractionRing A L] [Algebra k L] [IsScalarTower k A L]

/-- No separate function-field generation hypothesis is needed when the
original coordinate functions already generate the affine algebra. -/
theorem fraction_field_adjoin_original_coordinates
    (x : σ → A) (hx : Algebra.adjoin k (Set.range x) = ⊤) :
    IntermediateField.adjoin k (Set.range (fun i => algebraMap A L (x i))) = ⊤ := by
  let E := IntermediateField.adjoin k (Set.range (fun i => algebraMap A L (x i)))
  let g : A →ₐ[k] L := IsScalarTower.toAlgHom k A L
  have hle : Algebra.adjoin k (Set.range x) ≤ E.toSubalgebra.comap g := by
    apply Algebra.adjoin_le_iff.mpr
    rintro _ ⟨i, rfl⟩
    exact IntermediateField.subset_adjoin k _ ⟨i, rfl⟩
  have hmem (a : A) : algebraMap A L a ∈ E := by
    apply hle
    rw [hx]
    trivial
  apply top_unique
  intro y _
  obtain ⟨a, b, _, rfl⟩ := IsFractionRing.div_surjective A y
  exact E.div_mem (hmem a) (hmem b)

end DimensionFourDependence
