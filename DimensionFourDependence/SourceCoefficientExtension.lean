import DimensionFourDependence.CoefficientLocalization

/-! # Original source actions on coefficient tensor products

These explicit actions retain the original source ring, whose prime
contraction is part of the geometric hypothesis, across coefficient
extension of a coordinate localization.
-/

namespace DimensionFourDependence

open scoped TensorProduct

variable {R k S A E : Type*} [CommRing R] [CommRing k] [CommRing S]
  [CommRing A] [CommRing E] [Algebra R S] [Algebra k S] [Algebra k E]

/-- The original source action on a coefficient-extended coordinate ring. -/
@[instance_reducible]
noncomputable def sourceCoefficientExtensionAlgebra : Algebra R (S ⊗[k] E) :=
  Algebra.TensorProduct.leftAlgebra (R := k) (S := R) (A := S) (B := E)

/-- Original source functions enter the coefficient extension through
the original coordinate inclusion. -/
theorem sourceCoefficientExtension_scalarTower :
    letI : Algebra R (S ⊗[k] E) := sourceCoefficientExtensionAlgebra (R := R) (k := k) (S := S) (E := E)
    IsScalarTower R S (S ⊗[k] E) := by
  let : Algebra R (S ⊗[k] E) := sourceCoefficientExtensionAlgebra (R := R) (k := k) (S := S) (E := E)
  exact IsScalarTower.of_algebraMap_eq (R := R) (S := S) (A := S ⊗[k] E) (fun _ => rfl)

variable [Algebra R A] [Algebra k A] [Algebra S A]
  [IsScalarTower R S A] [IsScalarTower k S A]

/-- Extending a coordinate localization respects the same original
source action on the two tensor rings. -/
theorem coefficientLocalization_original_source_scalarTower :
    letI : Algebra R (S ⊗[k] E) := sourceCoefficientExtensionAlgebra (R := R) (k := k) (S := S) (E := E)
    letI : Algebra R (A ⊗[k] E) := sourceCoefficientExtensionAlgebra (R := R) (k := k) (S := A) (E := E)
    letI : Algebra (S ⊗[k] E) (A ⊗[k] E) :=
      (coefficientLocalizationHom (k := k) (S := S) (A := A) (E := E)).toRingHom.toAlgebra
    IsScalarTower R (S ⊗[k] E) (A ⊗[k] E) := by
  let : Algebra R (S ⊗[k] E) := sourceCoefficientExtensionAlgebra (R := R) (k := k) (S := S) (E := E)
  let : Algebra R (A ⊗[k] E) := sourceCoefficientExtensionAlgebra (R := R) (k := k) (S := A) (E := E)
  let : Algebra (S ⊗[k] E) (A ⊗[k] E) :=
    (coefficientLocalizationHom (k := k) (S := S) (A := A) (E := E)).toRingHom.toAlgebra
  apply IsScalarTower.of_algebraMap_eq
  intro r
  change algebraMap R A r ⊗ₜ[k] (1 : E) = algebraMap S A (algebraMap R S r) ⊗ₜ[k] (1 : E)
  rw [← IsScalarTower.algebraMap_apply R S A]

end DimensionFourDependence
