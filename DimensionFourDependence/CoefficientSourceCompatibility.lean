import DimensionFourDependence.LocalEquivCoefficientField

/-! # Coefficient descent preserves the actual source realization

Target compatibility and compatible field inclusions imply source
compatibility. These statements keep the complete elementwise conclusions
while avoiding repeated expansion of concrete projective chart instances.
-/

namespace DimensionFourDependence

variable {K C A B F : Type*} [Field K] [Field C]
  [CommRing A] [CommRing B] [CommRing F]
  [Algebra K C] [Algebra K A] [Algebra A B] [Algebra C B]
  [Algebra A F] [Algebra B F] [Algebra C F]
  [IsScalarTower A B F] [IsScalarTower C B F]

/-- Every descended coefficient retains its original source-field value. -/
def CoefficientSourceCompatible (f : C →ₐ[K] A) : Prop :=
  ∀ c : C, algebraMap A F (f c) = algebraMap C F c

/-- Compatibility with the upstairs local ring determines the original
function-field realization of a descended coefficient embedding. -/
theorem coefficient_target_compatible_source (f : C →ₐ[K] A)
    (h : CoefficientTargetCompatible (B := B) f) :
    CoefficientSourceCompatible (F := F) f := by
  intro c
  rw [IsScalarTower.algebraMap_apply A B F, h c,
    ← IsScalarTower.algebraMap_apply C B F]

end DimensionFourDependence
