import DimensionFourDependence.CoefficientLocalization
import DimensionFourDependence.SourceLocalNormalization
import DimensionFourDependence.UnramifiedDvrBaseChange

/-! # Normalized coordinate local rings after finite coefficient extension

Let a coordinate algebra localize to a source DVR whose parameter field
is relatively closed in the source function field. After finite
coefficient extension, the same source denominators identify the local
coordinate ring with a divisor localization of the finite étale source
base change. That ring is a DVR and is already normal, so the coordinate
normalization has exactly the same local ring at the contracted prime.
-/

namespace DimensionFourDependence

open scoped TensorProduct

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000

variable {k S A F E : Type*} [Field k] [CharZero k] [CommRing S]
  [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Field F] [Field E]
  [Algebra k S] [Algebra k A] [Algebra k F] [Algebra k E]
  [Algebra S A] [IsScalarTower k S A] [FaithfulSMul S A]
  [Algebra A F] [IsScalarTower k A F] [IsFractionRing A F] [Module.Finite k E]

local notation "Sₑ" => S ⊗[k] E
local notation "Aₑ" => A ⊗[k] E
local notation "Fₑ" => FractionRing (A ⊗[k] E)

/-- The precise local-ring identification, with all constructed
coefficient, fraction-field and normalization algebra structures retained. -/
noncomputable def CoefficientNormalizationLocalRing
    (hclosed : algebraicClosure k F = ⊥)
    (Q : Ideal Aₑ) [Q.IsPrime] [Q.LiesOver (IsLocalRing.maximalIdeal A)] : Prop :=
    letI : IsDomain Aₑ := relatively_closed_local_ring_base_change_isDomain hclosed
    letI : Algebra Sₑ Aₑ :=
      (coefficientLocalizationHom (k := k) (S := S) (A := A) (E := E)).toRingHom.toAlgebra
    letI : IsScalarTower Sₑ (Localization.AtPrime Q) Fₑ :=
      IsScalarTower.to₁₃₄ Sₑ Aₑ (Localization.AtPrime Q) Fₑ
    letI : IsDiscreteValuationRing (Localization.AtPrime Q) :=
      (relatively_closed_dvr_base_change_local hclosed Q).1
    letI : Algebra (integralClosure Sₑ Fₑ) (Localization.AtPrime Q) :=
      (integralClosureToNormalLocalHom (S := Sₑ) (A := Localization.AtPrime Q) (F := Fₑ)).toRingHom.toAlgebra
    IsLocalization.AtPrime (Localization.AtPrime Q)
      ((IsLocalRing.maximalIdeal (Localization.AtPrime Q)).under (integralClosure Sₑ Fₑ))

/-- The integral closure of the extended coordinate algebra has the same
local ring as the actual unramified source divisor extension. Its prime
is the contraction of the maximal ideal of that constructed DVR. -/
theorem coefficient_normalization_source_localization
    (hclosed : algebraicClosure k F = ⊥)
    (M : Submonoid S) [IsLocalization M A]
    (Q : Ideal Aₑ) [Q.IsPrime] [Q.LiesOver (IsLocalRing.maximalIdeal A)] :
    CoefficientNormalizationLocalRing (S := S) hclosed Q := by
  let : IsDomain Aₑ := relatively_closed_local_ring_base_change_isDomain hclosed
  let : Algebra Sₑ Aₑ :=
    (coefficientLocalizationHom (k := k) (S := S) (A := A) (E := E)).toRingHom.toAlgebra
  let : IsScalarTower Sₑ (Localization.AtPrime Q) Fₑ :=
    IsScalarTower.to₁₃₄ Sₑ Aₑ (Localization.AtPrime Q) Fₑ
  let : IsDiscreteValuationRing (Localization.AtPrime Q) :=
    (relatively_closed_dvr_base_change_local hclosed Q).1
  let : Algebra (integralClosure Sₑ Fₑ) (Localization.AtPrime Q) :=
    (integralClosureToNormalLocalHom (S := Sₑ) (A := Localization.AtPrime Q) (F := Fₑ)).toRingHom.toAlgebra
  let : FaithfulSMul Aₑ (Localization.AtPrime Q) := inferInstance
  let : FaithfulSMul Sₑ (Localization.AtPrime Q) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr (by
      intro x y hxy
      apply coefficientLocalizationHom_injective (k := k) (S := S) (A := A) (E := E)
      apply FaithfulSMul.algebraMap_injective Aₑ (Localization.AtPrime Q)
      change algebraMap Aₑ (Localization.AtPrime Q) (algebraMap Sₑ Aₑ x) =
        algebraMap Aₑ (Localization.AtPrime Q) (algebraMap Sₑ Aₑ y)
      simpa only [← IsScalarTower.algebraMap_apply Sₑ Aₑ (Localization.AtPrime Q)] using hxy)
  let : IsLocalization.AtPrime (Localization.AtPrime Q) (Q.under Sₑ) := coefficient_localization_atPrime M Q
  exact normalized_intermediate_algebra_source_localization (R := Sₑ) (S := Sₑ) (Q.under Sₑ)

end DimensionFourDependence
