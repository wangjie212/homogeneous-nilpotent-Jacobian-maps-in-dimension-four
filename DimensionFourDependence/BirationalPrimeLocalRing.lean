import DimensionFourDependence.PrimeLocalizationFunctionField
import DimensionFourDependence.IntermediateFunctionField
import DimensionFourDependence.ValuationLocalOverring

/-! # Contracted primes in birational source coordinate algebras

For an actual intermediate coordinate algebra inside the source function
field, the local map at primes lying over one another is constructed by
localization. Its chosen source-field inclusions agree. If the source
prime localization is a DVR, the dominating local overring is exactly
that source DVR, without an assumed parameter residue condition.
-/

namespace DimensionFourDependence

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000

variable {R S F : Type*} [CommRing R] [IsDomain R] [CommRing S] [IsDomain S] [Field F]
  [Algebra R S] [Algebra R F] [Algebra S F] [IsScalarTower R S F]
  [IsFractionRing R F] [FaithfulSMul S F]

omit [IsDomain R] [IsDomain S] in
/-- The local maps at contracted primes preserve the same actual source
function field with the explicitly chosen prime-local inclusions. -/
theorem prime_localizations_same_field_scalarTower
    (Q : Ideal R) [Q.IsPrime] (P : Ideal S) [P.IsPrime] [P.LiesOver Q] :
    letI : Algebra (Localization.AtPrime Q) F := primeLocalizationFractionAlgebra Q
    letI : Algebra (Localization.AtPrime P) F := primeLocalizationFractionAlgebra P
    letI : Algebra (Localization.AtPrime Q) (Localization.AtPrime P) :=
      Localization.AtPrime.algebraOfLiesOver Q P
    IsScalarTower (Localization.AtPrime Q) (Localization.AtPrime P) F := by
  let : Algebra (Localization.AtPrime Q) F := primeLocalizationFractionAlgebra Q
  let : Algebra (Localization.AtPrime P) F := primeLocalizationFractionAlgebra P
  let : Algebra (Localization.AtPrime Q) (Localization.AtPrime P) :=
    Localization.AtPrime.algebraOfLiesOver Q P
  let : IsScalarTower R (Localization.AtPrime Q) F := primeLocalizationFraction_scalarTower Q
  let : IsScalarTower S (Localization.AtPrime P) F := primeLocalizationFraction_scalarTower P
  let : IsScalarTower R (Localization.AtPrime P) F := IsScalarTower.to₁₃₄ R S (Localization.AtPrime P) F
  apply IsScalarTower.of_algebraMap_eq'
  apply IsLocalization.ringHom_ext Q.primeCompl
  ext r
  change algebraMap (Localization.AtPrime Q) F (algebraMap R (Localization.AtPrime Q) r) =
    algebraMap (Localization.AtPrime P) F
      (algebraMap (Localization.AtPrime Q) (Localization.AtPrime P) (algebraMap R (Localization.AtPrime Q) r))
  rw [← IsScalarTower.algebraMap_apply R (Localization.AtPrime Q) F,
    ← IsScalarTower.algebraMap_apply R (Localization.AtPrime Q) (Localization.AtPrime P),
    ← IsScalarTower.algebraMap_apply R (Localization.AtPrime P) F]

omit [IsDomain R] [IsDomain S] in
/-- Contracted-prime localization maps are local homomorphisms. -/
theorem contracted_prime_localization_isLocalHom
    (Q : Ideal R) [Q.IsPrime] (P : Ideal S) [P.IsPrime] [P.LiesOver Q] :
    letI : Algebra (Localization.AtPrime Q) (Localization.AtPrime P) :=
      Localization.AtPrime.algebraOfLiesOver Q P
    IsLocalHom (algebraMap (Localization.AtPrime Q) (Localization.AtPrime P)) := by
  let : Algebra (Localization.AtPrime Q) (Localization.AtPrime P) :=
    Localization.AtPrime.algebraOfLiesOver Q P
  exact Localization.isLocalHom_localRingHom Q P (algebraMap R S) Ideal.LiesOver.over

include F in
/-- A coordinate prime above an actual source DVR has that same local
ring when the coordinate algebra is birational inside the source field. -/
theorem birational_prime_source_local_map_bijective
    (Q : Ideal R) [Q.IsPrime] [IsDiscreteValuationRing (Localization.AtPrime Q)]
    (P : Ideal S) [P.IsPrime] [P.LiesOver Q] :
    letI : Algebra (Localization.AtPrime Q) (Localization.AtPrime P) :=
      Localization.AtPrime.algebraOfLiesOver Q P
    Function.Bijective (algebraMap (Localization.AtPrime Q) (Localization.AtPrime P)) := by
  let : Algebra (Localization.AtPrime Q) (Localization.AtPrime P) :=
    Localization.AtPrime.algebraOfLiesOver Q P
  let : Algebra (Localization.AtPrime Q) F := primeLocalizationFractionAlgebra Q
  let : Algebra (Localization.AtPrime P) F := primeLocalizationFractionAlgebra P
  let : IsScalarTower (Localization.AtPrime Q) (Localization.AtPrime P) F :=
    prime_localizations_same_field_scalarTower Q P
  let : IsFractionRing (Localization.AtPrime Q) F := primeLocalizationFraction_isFractionRing Q
  let : IsFractionRing S F := intermediate_algebra_same_fraction_field (R := R)
  let : IsFractionRing (Localization.AtPrime P) F := primeLocalizationFraction_isFractionRing P
  let : FaithfulSMul (Localization.AtPrime P) F :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr (IsFractionRing.injective (Localization.AtPrime P) F)
  let : IsLocalHom (algebraMap (Localization.AtPrime Q) (Localization.AtPrime P)) :=
    contracted_prime_localization_isLocalHom Q P
  exact valuation_local_overring_algebraMap_bijective
    (A := Localization.AtPrime Q) (B := Localization.AtPrime P) (F := F)

/-- The actual birational contracted-prime local isomorphism over the
source DVR, given by its original localized source map. -/
noncomputable def birationalPrimeSourceLocalEquiv
    (Q : Ideal R) [Q.IsPrime] [IsDiscreteValuationRing (Localization.AtPrime Q)]
    (P : Ideal S) [P.IsPrime] [P.LiesOver Q] :
    letI : Algebra (Localization.AtPrime Q) (Localization.AtPrime P) :=
      Localization.AtPrime.algebraOfLiesOver Q P
    Localization.AtPrime Q ≃ₐ[Localization.AtPrime Q] Localization.AtPrime P := by
  let : Algebra (Localization.AtPrime Q) (Localization.AtPrime P) :=
    Localization.AtPrime.algebraOfLiesOver Q P
  exact AlgEquiv.ofBijective (Algebra.ofId _ _) (birational_prime_source_local_map_bijective (F := F) Q P)

end DimensionFourDependence
