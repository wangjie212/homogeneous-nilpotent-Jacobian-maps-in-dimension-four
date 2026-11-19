import DimensionFourDependence.CompatibleFullOutputEmbedding
import DimensionFourDependence.AlgebraicConstantsCompatibleImages

/-! # Original algebraic fiber coefficients are algebraic over a realized target field -/

namespace DimensionFourDependence

set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 100000

variable {K S C J G : Type*} [Field K] [Field S] [Field C] [Field J] [Field G]
  [Algebra K S] [Algebra K J] [Algebra K G] [Algebra J G] [IsScalarTower K J G]
  {n : ℕ}

/-- When all actual original output values belong to a specified
realized target field, every original algebraic fiber coefficient is
algebraic over that same target field, in the same source realization. -/
theorem realized_full_output_values_make_original_fiber_coefficients_algebraic
    (H : Fin n → S) [Algebra (fullOutputField (K := K) H) C]
    [Algebra C S] [IsScalarTower (fullOutputField (K := K) H) C S]
    [Algebra.IsAlgebraic (fullOutputField (K := K) H) C]
    (Φ : S →ₐ[K] G) (Y : Fin n → J)
    (hY : ∀ i, Φ (H i) = algebraMap J G (Y i)) (c : C) :
    IsAlgebraic J (Φ (algebraMap C S c)) := by
  let Γ := IsScalarTower.toAlgHom K J G
  let δ := compatibleFullOutputFieldHom Φ Γ H Y hY
  let a : fullOutputField (K := K) H →+* G :=
    Φ.toRingHom.comp (fullOutputField (K := K) H).val.toRingHom
  let b : C →+* G := Φ.toRingHom.comp (algebraMap C S)
  have hcompat (m : fullOutputField (K := K) H) : b (algebraMap _ C m) = a m := by
    change Φ (algebraMap C S (algebraMap (fullOutputField (K := K) H) C m)) = Φ (m : S)
    rw [← IsScalarTower.algebraMap_apply (fullOutputField (K := K) H) C S]
    rfl
  have ha (m : fullOutputField (K := K) H) : IsAlgebraic J (a m) := by
    have he := compatibleFullOutputFieldHom_source_value Φ Γ H Y hY m
    change algebraMap J G (δ m) = a m at he
    rw [← he]
    exact isAlgebraic_algebraMap _
  exact compatible_algebraic_constant_extension_images_algebraic a b hcompat ha c

end DimensionFourDependence
