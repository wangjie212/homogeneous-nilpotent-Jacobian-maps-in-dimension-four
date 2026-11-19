import DimensionFourDependence.Defs
import Mathlib.RingTheory.Localization.LocalizationLocalization

/-! # Local rings at primes surviving a source denominator localization

A prime disjoint from the source denominators extends to a prime in the
localized ring. The original and extended prime local rings are the same
actual source localization. This direction starts with the original
prime, as needed for a curve in the coordinate normalization.
-/

namespace DimensionFourDependence

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
  (M : Submonoid R) [IsLocalization M A]

/-- The local ring at the extended prime is the original prime local
ring, with its actual source coordinate map. -/
theorem denominator_prime_source_localization
    (q : Ideal R) [q.IsPrime] (hM : Disjoint (M : Set R) (q : Set R)) :
    let P := q.map (algebraMap R A)
    letI : P.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint M A q inferInstance hM
    IsLocalization.AtPrime (Localization.AtPrime P) q := by
  let P := q.map (algebraMap R A)
  let : P.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint M A q inferInstance hM
  have hunder : P.under R = q := IsLocalization.under_map_of_isPrime_disjoint M A inferInstance hM
  have h : IsLocalization.AtPrime (Localization.AtPrime P) (P.under R) :=
    IsLocalization.isLocalization_isLocalization_atPrime_isLocalization M (Localization.AtPrime P) P
  have hcompl : (P.under R).primeCompl = q.primeCompl := by
    apply Submonoid.ext
    intro r
    change r ∉ P.under R ↔ r ∉ q
    rw [hunder]
  change IsLocalization (P.under R).primeCompl (Localization.AtPrime P) at h
  change IsLocalization q.primeCompl (Localization.AtPrime P)
  rwa [hcompl] at h

/-- The explicit local algebra isomorphism from a prime of the original
coordinate ring to its surviving prime in the denominator localization. -/
noncomputable def denominatorPrimeLocalEquiv
    (q : Ideal R) [q.IsPrime] (hM : Disjoint (M : Set R) (q : Set R)) :
    let P := q.map (algebraMap R A)
    letI : P.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint M A q inferInstance hM
    Localization.AtPrime q ≃ₐ[R] Localization.AtPrime P := by
  let P := q.map (algebraMap R A)
  let : P.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint M A q inferInstance hM
  let : IsLocalization.AtPrime (Localization.AtPrime P) q := denominator_prime_source_localization M q hM
  exact IsLocalization.algEquiv q.primeCompl _ _

end DimensionFourDependence
