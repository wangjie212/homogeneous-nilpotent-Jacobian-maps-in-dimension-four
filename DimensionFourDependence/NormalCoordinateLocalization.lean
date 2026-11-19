import DimensionFourDependence.IntermediateDenominatorLocalization
import DimensionFourDependence.SourceLocalNormalization

/-! # Normal coordinate localizations are localizations of normalization

If a source denominator localization is normal already, normalizing the
original coordinate algebra and inverting those same denominators gives
that normal ring itself. This applies to the finite étale coefficient
base change of the source DVR, before choosing any upstairs prime.
-/

namespace DimensionFourDependence

variable {S A F : Type*} [CommRing S] [CommRing A] [Field F]
  [Algebra S A] [Algebra S F] [Algebra A F] [IsScalarTower S A F]
  [IsFractionRing A F] [IsIntegrallyClosed A]

/-- The actual integral closure localizes to an already normal source
denominator localization, using the constructed same-function map. -/
theorem integralClosure_normal_denominator_localization
    (M : Submonoid S) [IsLocalization M A] :
    letI : Algebra (integralClosure S F) A :=
      (integralClosureToNormalLocalHom (S := S) (A := A) (F := F)).toRingHom.toAlgebra
    IsLocalization (Algebra.algebraMapSubmonoid (integralClosure S F) M) A := by
  let : Algebra (integralClosure S F) A :=
    (integralClosureToNormalLocalHom (S := S) (A := A) (F := F)).toRingHom.toAlgebra
  let : FaithfulSMul (integralClosure S F) A :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr integralClosureToNormalLocalHom_injective
  let : IsScalarTower S (integralClosure S F) A := IsScalarTower.of_algebraMap_eq
    (fun s => ((integralClosureToNormalLocalHom (S := S) (A := A) (F := F)).commutes s).symm)
  exact intermediate_algebra_denominator_localization M

end DimensionFourDependence
