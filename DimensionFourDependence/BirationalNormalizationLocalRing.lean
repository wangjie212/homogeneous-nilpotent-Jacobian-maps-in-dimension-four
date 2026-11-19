import DimensionFourDependence.BirationalPrimeLocalRing
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed

/-! # Normalized coordinate primes above a source DVR

The actual integral closure of an intermediate coordinate algebra still
embeds in the original source function field. Its primes above a source
DVR therefore have that same source local ring. The proposition retains
the explicit normalization and contracted-prime localization maps.
-/

namespace DimensionFourDependence

variable {R S F : Type*} [CommRing R] [IsDomain R] [CommRing S] [IsDomain S] [Field F]
  [Algebra R S] [Algebra R F] [Algebra S F] [IsScalarTower R S F]
  [IsFractionRing R F] [FaithfulSMul S F]

/-- The full normalized-prime local map statement, with the actual
source-to-normalization coefficient action explicitly specified. -/
noncomputable def BirationalNormalizationLocalMapBijective (Q : Ideal R) [Q.IsPrime] : Prop :=
  letI : Algebra R (integralClosure S F) :=
    ((algebraMap S (integralClosure S F)).comp (algebraMap R S)).toAlgebra
  ∀ (P : Ideal (integralClosure S F)) [P.IsPrime] [P.LiesOver Q],
    letI : Algebra (Localization.AtPrime Q) (Localization.AtPrime P) :=
      Localization.AtPrime.algebraOfLiesOver Q P
    Function.Bijective (algebraMap (Localization.AtPrime Q) (Localization.AtPrime P))

omit [IsDomain S] [FaithfulSMul S F] in
/-- Normalized coordinate primes above a source DVR recover exactly that
same local source ring through the original localized source map. -/
theorem birational_normalization_local_map_bijective
    (Q : Ideal R) [Q.IsPrime] [IsDiscreteValuationRing (Localization.AtPrime Q)] :
    BirationalNormalizationLocalMapBijective (S := S) (F := F) Q := by
  let : Algebra R (integralClosure S F) :=
    ((algebraMap S (integralClosure S F)).comp (algebraMap R S)).toAlgebra
  let : IsScalarTower R S (integralClosure S F) := IsScalarTower.of_algebraMap_eq (by intro r; rfl)
  intro P hP hlie
  let : IsScalarTower R (integralClosure S F) F := IsScalarTower.to₁₃₄ R S (integralClosure S F) F
  let : FaithfulSMul (integralClosure S F) F :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr Subtype.val_injective
  exact birational_prime_source_local_map_bijective (F := F) Q P

end DimensionFourDependence
