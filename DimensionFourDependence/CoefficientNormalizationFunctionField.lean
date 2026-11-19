import DimensionFourDependence.CoefficientLocalization
import DimensionFourDependence.LocalizationFunctionField
import DimensionFourDependence.NormalizationRing

/-! # Canonical normalization in the extended source function field

The field used for the normalized horizontal local model is the actual
fraction field of the extended coordinate algebra. Thus its integral
closure is identified with the canonical coordinate normalization, not
merely with an integral closure in an unspecified extension field.
-/

namespace DimensionFourDependence

open scoped TensorProduct

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000

variable {k S A E : Type*} [CommRing k] [CommRing S] [CommRing A] [CommRing E]
  [Algebra k S] [Algebra k A] [Algebra k E] [Algebra S A] [IsScalarTower k S A]
  [Module.Flat k E] [FaithfulSMul S A] [IsDomain (A ⊗[k] E)]

/-- The extended source fraction field is an actual fraction field of
the extended coordinate algebra, using the original tensor inclusion. -/
theorem coefficient_localization_same_fraction_field
    (M : Submonoid S) [IsLocalization M A] :
    letI : Algebra (S ⊗[k] E) (A ⊗[k] E) :=
      (coefficientLocalizationHom (k := k) (S := S) (A := A) (E := E)).toRingHom.toAlgebra
    IsFractionRing (S ⊗[k] E) (FractionRing (A ⊗[k] E)) := by
  let : Algebra (S ⊗[k] E) (A ⊗[k] E) :=
    (coefficientLocalizationHom (k := k) (S := S) (A := A) (E := E)).toRingHom.toAlgebra
  let : IsDomain (S ⊗[k] E) := Function.Injective.isDomain
    (coefficientLocalizationHom (k := k) (S := S) (A := A) (E := E)) coefficientLocalizationHom_injective
  let : FaithfulSMul (S ⊗[k] E) (A ⊗[k] E) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr coefficientLocalizationHom_injective
  let : IsLocalization (Algebra.algebraMapSubmonoid (S ⊗[k] E) M) (A ⊗[k] E) :=
    coefficient_localization_isLocalization M
  exact source_localization_same_fraction_field (B := A ⊗[k] E)
    (Algebra.algebraMapSubmonoid (S ⊗[k] E) M)

/-- The coordinate and source fraction fields are canonically identified
over the entire coefficient-extended coordinate algebra. -/
noncomputable def coefficientLocalizationFunctionFieldEquiv
    (M : Submonoid S) [IsLocalization M A] :
    letI : Algebra (S ⊗[k] E) (A ⊗[k] E) :=
      (coefficientLocalizationHom (k := k) (S := S) (A := A) (E := E)).toRingHom.toAlgebra
    FractionRing (S ⊗[k] E) ≃ₐ[S ⊗[k] E] FractionRing (A ⊗[k] E) := by
  let : Algebra (S ⊗[k] E) (A ⊗[k] E) :=
    (coefficientLocalizationHom (k := k) (S := S) (A := A) (E := E)).toRingHom.toAlgebra
  let : IsFractionRing (S ⊗[k] E) (FractionRing (A ⊗[k] E)) := coefficient_localization_same_fraction_field M
  exact IsLocalization.algEquiv (nonZeroDivisors (S ⊗[k] E)) _ _

/-- The canonical normalization of the extended coordinate ring is its
integral closure in the extended source function field used by the local
normalization theorem. -/
noncomputable def coefficientCoordinateNormalizationFunctionFieldEquiv
    (M : Submonoid S) [IsLocalization M A] :
    letI : Algebra (S ⊗[k] E) (A ⊗[k] E) :=
      (coefficientLocalizationHom (k := k) (S := S) (A := A) (E := E)).toRingHom.toAlgebra
    normalizationRing (S ⊗[k] E) ≃ₐ[S ⊗[k] E]
      integralClosure (S ⊗[k] E) (FractionRing (A ⊗[k] E)) := by
  let : Algebra (S ⊗[k] E) (A ⊗[k] E) :=
    (coefficientLocalizationHom (k := k) (S := S) (A := A) (E := E)).toRingHom.toAlgebra
  exact (coefficientLocalizationFunctionFieldEquiv (E := E) M).mapIntegralClosure

end DimensionFourDependence
