import DimensionFourDependence.SourceCoefficientExtension
import DimensionFourDependence.CoordinateLocalizationFunctionField
import DimensionFourDependence.NormalizedPrimeUnramifiedModel
import DimensionFourDependence.UnramifiedDvrBaseChange

/-! # Given canonical normalization primes after finite coefficient extension

A source-coordinate denominator model extends through finite coefficient
base change. Every given prime of the canonical extended coordinate
normalization over the original source divisor has its own unramified
source-DVR local model. The canonical normalization is formed in its
original fraction field and is not replaced by an assumed local model.
-/

namespace DimensionFourDependence

open scoped TensorProduct

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000

variable {R k S A F E : Type*} [CommRing R] [Field k] [CharZero k]
  [CommRing S] [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  [Field F] [Field E] [Algebra R S] [Algebra R A]
  [Algebra k S] [Algebra k A] [Algebra k F] [Algebra k E]
  [Algebra S A] [IsScalarTower R S A] [IsScalarTower k S A] [FaithfulSMul S A]
  [Algebra A F] [IsScalarTower k A F] [IsFractionRing A F] [Module.Finite k E]

local notation "Sₑ" => S ⊗[k] E
local notation "Aₑ" => A ⊗[k] E
local notation "M₀" Q => Algebra.algebraMapSubmonoid S (Ideal.primeCompl Q)
local notation "Mₑ" Q => Algebra.algebraMapSubmonoid Sₑ (M₀ Q)

/-- Full canonical-normalization prime model, with the source actions,
normal source model, and its canonical coordinate fraction realization. -/
noncomputable def CoefficientCanonicalNormalizationPrimeModel
    (hclosed : algebraicClosure k F = ⊥) (Q : Ideal R) [Q.IsPrime]
    [IsLocalization (M₀ Q) A] : Prop :=
  letI : IsDomain Aₑ := relatively_closed_local_ring_base_change_isDomain hclosed
  letI : IsDedekindDomain Aₑ := relatively_closed_dvr_base_change_dedekind hclosed
  letI : IsDomain Sₑ := Function.Injective.isDomain
    (coefficientLocalizationHom (k := k) (S := S) (A := A) (E := E)) coefficientLocalizationHom_injective
  letI : Algebra Sₑ Aₑ :=
    (coefficientLocalizationHom (k := k) (S := S) (A := A) (E := E)).toRingHom.toAlgebra
  letI : FaithfulSMul Sₑ Aₑ :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr coefficientLocalizationHom_injective
  letI : IsLocalization (Mₑ Q) Aₑ := coefficient_localization_isLocalization (M₀ Q)
  letI : Algebra Aₑ (FractionRing Sₑ) := coordinateLocalizationCanonicalFractionAlgebra (A := Aₑ) (Mₑ Q)
  letI : IsScalarTower Sₑ Aₑ (FractionRing Sₑ) := coordinateLocalizationCanonicalFraction_scalarTower (Mₑ Q)
  letI : IsFractionRing Aₑ (FractionRing Sₑ) := coordinateLocalizationCanonicalFraction_isFractionRing (Mₑ Q)
  letI : Algebra R Sₑ := sourceCoefficientExtensionAlgebra (R := R) (k := k) (S := S) (E := E)
  letI : Algebra R Aₑ := sourceCoefficientExtensionAlgebra (R := R) (k := k) (S := A) (E := E)
  NormalizedPrimeUnramifiedSourceModel (S := Sₑ) (O := A) (B := Aₑ) (F := FractionRing Sₑ) Q

/-- A given canonical normalization prime over the source divisor has
an unramified DVR local model after finite coefficient extension. -/
theorem coefficient_canonical_normalization_prime_model
    (hclosed : algebraicClosure k F = ⊥) (Q : Ideal R) [Q.IsPrime]
    [IsLocalization.AtPrime A Q] [IsLocalization (M₀ Q) A] :
    CoefficientCanonicalNormalizationPrimeModel (R := R) (k := k) (S := S)
      (A := A) (F := F) (E := E) hclosed Q := by
  let : IsDomain Aₑ := relatively_closed_local_ring_base_change_isDomain hclosed
  let : IsDedekindDomain Aₑ := relatively_closed_dvr_base_change_dedekind hclosed
  let : IsDomain Sₑ := Function.Injective.isDomain
    (coefficientLocalizationHom (k := k) (S := S) (A := A) (E := E)) coefficientLocalizationHom_injective
  let : Algebra Sₑ Aₑ :=
    (coefficientLocalizationHom (k := k) (S := S) (A := A) (E := E)).toRingHom.toAlgebra
  let : FaithfulSMul Sₑ Aₑ :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr coefficientLocalizationHom_injective
  let : IsLocalization (Mₑ Q) Aₑ := coefficient_localization_isLocalization (M₀ Q)
  let : Algebra Aₑ (FractionRing Sₑ) := coordinateLocalizationCanonicalFractionAlgebra (A := Aₑ) (Mₑ Q)
  let : IsScalarTower Sₑ Aₑ (FractionRing Sₑ) := coordinateLocalizationCanonicalFraction_scalarTower (Mₑ Q)
  let : IsFractionRing Aₑ (FractionRing Sₑ) := coordinateLocalizationCanonicalFraction_isFractionRing (Mₑ Q)
  let : Algebra R Sₑ := sourceCoefficientExtensionAlgebra (R := R) (k := k) (S := S) (E := E)
  let : Algebra R Aₑ := sourceCoefficientExtensionAlgebra (R := R) (k := k) (S := A) (E := E)
  let : IsScalarTower R S Sₑ := sourceCoefficientExtension_scalarTower
  let : IsScalarTower R A Aₑ := sourceCoefficientExtension_scalarTower
  let : IsScalarTower R Sₑ Aₑ := coefficientLocalization_original_source_scalarTower
  let : IsLocalization (Algebra.algebraMapSubmonoid Sₑ Q.primeCompl) Aₑ := by
    rw [← Algebra.algebraMapSubmonoid_map_map (A := S) (B := Sₑ)]
    infer_instance
  let : Algebra.Etale A Aₑ := (finite_coefficient_base_change_etale (k := k) (A := A) (E := E)).2
  exact normalized_prime_unramified_source_model (S := Sₑ) (O := A) (B := Aₑ) (F := FractionRing Sₑ) Q

end DimensionFourDependence
