import DimensionFourDependence.NormalCodimensionOneRegularity
import Mathlib.RingTheory.Localization.LocalizationLocalization

/-! # Prime localization of a localization preserves actual field regularity -/

namespace DimensionFourDependence

variable {A T F : Type*} [CommRing A] [IsDomain A] [CommRing T] [Field F]
  [Algebra A T] [Algebra A F] [Algebra T F] [IsScalarTower A T F] [IsFractionRing A F]

/-- Any specified realization of the original prime localization
in the same fraction field has exactly the canonical regular fractions. -/
theorem prime_localization_integer_iff_fraction_subalgebra
    (P : Ideal A) [P.IsPrime] [IsLocalization.AtPrime T P] (x : F) :
    IsLocalization.IsInteger T x ↔ x ∈ fractionPrimeLocalAlgebra A P := by
  have hmap : Localization.mapToFractionRing F P.primeCompl T P.primeCompl_le_nonZeroDivisors =
      IsScalarTower.toAlgHom A T F := by
    apply IsLocalization.algHom_ext P.primeCompl
    ext
  have he := Localization.subalgebra.mem_range_mapToFractionRing_iff_ofField
    F P.primeCompl P.primeCompl_le_nonZeroDivisors T x
  rw [hmap] at he
  exact he

variable {R : Type*} [CommRing R] [IsDomain R]
  [Algebra A R] [Algebra R F] [IsScalarTower A R F] [IsFractionRing R F]

/-- Localizing the actual intermediate local ring at one of its
primes gives the same regular fractions as localizing the original
ring at the contracted prime, with no field isomorphism supplied. -/
theorem iterated_prime_fraction_membership_iff_under
    (M : Submonoid A) [IsLocalization M R]
    (Q : Ideal R) [Q.IsPrime] (x : F) :
    x ∈ fractionPrimeLocalAlgebra R Q ↔
      x ∈ fractionPrimeLocalAlgebra A (Q.comap (algebraMap A R)) := by
  let S := fractionPrimeLocalAlgebra (F := F) R Q
  let : Algebra A S := ((algebraMap R S).comp (algebraMap A R)).toAlgebra
  let : IsScalarTower A R S := IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower A S F := IsScalarTower.of_algebraMap_eq' (by
    ext a
    exact IsScalarTower.algebraMap_apply A R F a)
  let : IsLocalization.AtPrime S (Q.comap (algebraMap A R)) :=
    IsLocalization.isLocalization_isLocalization_atPrime_isLocalization (S := R) M S Q
  have he := prime_localization_integer_iff_fraction_subalgebra
    (T := S) (Q.comap (algebraMap A R)) x
  have hx : x ∈ fractionPrimeLocalAlgebra R Q ↔ IsLocalization.IsInteger S x := by
    constructor
    · intro h
      exact ⟨⟨x, h⟩, rfl⟩
    · rintro ⟨y, hy⟩
      exact hy ▸ y.property
  exact hx.trans he

/-- Contraction from a localization preserves the prime's height,
including the height-one divisor test used in the vertex stalk. -/
theorem localized_prime_under_height_eq
    (M : Submonoid A) [IsLocalization M R] (Q : Ideal R) [Q.IsPrime] :
    (Q.comap (algebraMap A R)).height = Q.height := by
  exact IsLocalization.height_under M Q

end DimensionFourDependence
