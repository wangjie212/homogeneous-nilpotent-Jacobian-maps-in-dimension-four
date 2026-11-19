import DimensionFourDependence.LocalizationFunctionField

/-! # A denominator model in the coordinate ring's canonical fraction field

The normal source model can be realized in the canonical coordinate
fraction field. Its normalization is then literally the canonical
coordinate normalization, so a given prime needs no change of field.
-/

namespace DimensionFourDependence

variable {S A : Type*} [CommRing S] [IsDomain S] [CommRing A] [IsDomain A]
  [Algebra S A] [FaithfulSMul S A] (M : Submonoid S) [IsLocalization M A]

/-- The coordinate and source denominator fraction fields are explicitly
identified over the original coordinate ring. -/
noncomputable def coordinateLocalizationFractionEquiv :
    FractionRing S ≃ₐ[S] FractionRing A := by
  let : IsFractionRing S (FractionRing A) :=
    source_localization_same_fraction_field (B := A) (L := FractionRing A) M
  exact IsLocalization.algEquiv (nonZeroDivisors S) _ _

/-- The source denominator ring in the canonical coordinate fraction field. -/
noncomputable def coordinateLocalizationCanonicalFractionHom : A →ₐ[S] FractionRing S :=
  (coordinateLocalizationFractionEquiv (A := A) M).symm.toAlgHom.comp
    (IsScalarTower.toAlgHom S A (FractionRing A))

/-- The chosen coordinate-fraction-field action of the denominator model. -/
@[instance_reducible]
noncomputable def coordinateLocalizationCanonicalFractionAlgebra : Algebra A (FractionRing S) :=
  (coordinateLocalizationCanonicalFractionHom (A := A) M).toRingHom.toAlgebra

/-- The normal source denominator realization preserves the original
coordinate inclusion in its canonical fraction field. -/
theorem coordinateLocalizationCanonicalFraction_scalarTower :
    letI : Algebra A (FractionRing S) := coordinateLocalizationCanonicalFractionAlgebra (A := A) M
    IsScalarTower S A (FractionRing S) := by
  let : Algebra A (FractionRing S) := coordinateLocalizationCanonicalFractionAlgebra (A := A) M
  exact IsScalarTower.of_algebraMap_eq
    (fun s => ((coordinateLocalizationCanonicalFractionHom (A := A) M).commutes s).symm)

/-- The canonical coordinate fraction field is also the actual fraction
field of the source denominator model, with its constructed map. -/
theorem coordinateLocalizationCanonicalFraction_isFractionRing :
    letI : Algebra A (FractionRing S) := coordinateLocalizationCanonicalFractionAlgebra (A := A) M
    IsFractionRing A (FractionRing S) := by
  let : Algebra A (FractionRing S) := coordinateLocalizationCanonicalFractionAlgebra (A := A) M
  let : IsScalarTower S A (FractionRing S) :=
    coordinateLocalizationCanonicalFraction_scalarTower M
  exact IsFractionRing.isFractionRing_of_isDomain_of_isLocalization M A (FractionRing S)

end DimensionFourDependence
