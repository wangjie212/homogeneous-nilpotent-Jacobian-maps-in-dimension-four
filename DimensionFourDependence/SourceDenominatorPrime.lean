import DimensionFourDependence.NormalizedPrimeLocalization
import Mathlib.RingTheory.Ideal.Over

/-! # Normalization primes over a source divisor survive its denominators

Contraction to an actual source divisor implies denominator avoidance.
Consequently a given prime of coordinate normalization, rather than a
preselected prime in a source model, has its local ring identified in the
normal source-denominator localization.
-/

namespace DimensionFourDependence

variable {R S N : Type*} [CommRing R] [CommRing S] [CommRing N]
  [Algebra R S] [Algebra R N] [Algebra S N] [IsScalarTower R S N]

/-- Lying over the source divisor makes the images of its complementary
denominators disjoint from the given coordinate prime. -/
theorem source_denominators_disjoint_of_liesOver
    (Q : Ideal R) [Q.IsPrime] (q : Ideal N) [q.LiesOver Q] :
    Disjoint (Algebra.algebraMapSubmonoid N (Algebra.algebraMapSubmonoid S Q.primeCompl) : Set N)
      (q : Set N) := by
  rw [Algebra.algebraMapSubmonoid_map_map]
  exact Ideal.disjoint_primeCompl_of_liesOver q Q

variable {A F : Type*} [CommRing A] [Field F]
  [Algebra S A] [Algebra S F] [Algebra A F] [IsScalarTower S A F]
  [IsFractionRing A F] [IsIntegrallyClosed A]

omit [CommRing N] [Algebra R N] [Algebra S N] [IsScalarTower R S N] in
/-- The local ring of a given normalization prime over a source divisor
is the local ring of its extended prime in the normal source model.
Denominator avoidance is derived from contraction. -/
theorem normalized_prime_over_source_local_equiv
    (Q : Ideal R) [Q.IsPrime]
    [IsLocalization (Algebra.algebraMapSubmonoid S Q.primeCompl) A] :
    letI : Algebra R (integralClosure S F) :=
      ((algebraMap S (integralClosure S F)).comp (algebraMap R S)).toAlgebra
    ∀ (q : Ideal (integralClosure S F)) [q.IsPrime] [q.LiesOver Q],
      letI : Algebra (integralClosure S F) A :=
        (integralClosureToNormalLocalHom (S := S) (A := A) (F := F)).toRingHom.toAlgebra
      let P := q.map (algebraMap (integralClosure S F) A)
      ∃ hP : P.IsPrime,
        @Nonempty (Localization.AtPrime q ≃ₐ[integralClosure S F] @Localization.AtPrime A _ P hP) := by
  let : Algebra R (integralClosure S F) :=
    ((algebraMap S (integralClosure S F)).comp (algebraMap R S)).toAlgebra
  let : IsScalarTower R S (integralClosure S F) := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  intro q hq hlie
  have hM := source_denominators_disjoint_of_liesOver (S := S) Q q
  let : Algebra (integralClosure S F) A :=
    (integralClosureToNormalLocalHom (S := S) (A := A) (F := F)).toRingHom.toAlgebra
  let : IsLocalization
      (Algebra.algebraMapSubmonoid (integralClosure S F)
        (Algebra.algebraMapSubmonoid S Q.primeCompl)) A :=
    integralClosure_normal_denominator_localization (Algebra.algebraMapSubmonoid S Q.primeCompl)
  let P := q.map (algebraMap (integralClosure S F) A)
  let hP : P.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint
    (Algebra.algebraMapSubmonoid (integralClosure S F)
      (Algebra.algebraMapSubmonoid S Q.primeCompl)) A q inferInstance hM
  exact ⟨hP, ⟨normalizedPrimeNormalSourceLocalEquiv
    (A := A) (Algebra.algebraMapSubmonoid S Q.primeCompl) q hM⟩⟩

end DimensionFourDependence
