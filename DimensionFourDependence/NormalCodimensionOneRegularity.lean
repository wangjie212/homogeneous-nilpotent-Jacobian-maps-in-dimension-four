import DimensionFourDependence.NormalFractionPolePrime
import Mathlib.RingTheory.Localization.AsSubring

/-! # Regularity detected at the height-one primes

All localizations are actual subalgebras of the specified fraction field.
The denominator-ideal criterion and the constructed height-one pole give
the codimension-one regularity theorem for normal Noetherian domains.
-/

namespace DimensionFourDependence

variable (R : Type*) {F : Type*} [CommRing R] [IsDomain R] [Field F]
  [Algebra R F] [IsFractionRing R F]

/-- The original prime localization, realized inside the specified
function field with the original coefficient-ring map. -/
noncomputable def fractionPrimeLocalAlgebra (P : Ideal R) [P.IsPrime] : Subalgebra R F :=
  Localization.subalgebra.ofField F P.primeCompl P.primeCompl_le_nonZeroDivisors

/-- The realized subalgebra is the localization at the original prime. -/
theorem fractionPrimeLocalAlgebra_isLocalization (P : Ideal R) [P.IsPrime] :
    IsLocalization.AtPrime (fractionPrimeLocalAlgebra (F := F) R P) P :=
  Localization.subalgebra.isLocalization_ofField F P.primeCompl P.primeCompl_le_nonZeroDivisors

attribute [instance] fractionPrimeLocalAlgebra_isLocalization

/-- The realized prime localization has its canonical local-ring structure. -/
theorem fractionPrimeLocalAlgebra_isLocalRing (P : Ideal R) [P.IsPrime] :
    IsLocalRing (fractionPrimeLocalAlgebra (F := F) R P) :=
  IsLocalization.AtPrime.isLocalRing _ P

attribute [instance] fractionPrimeLocalAlgebra_isLocalRing

/-- A fraction is regular at a prime exactly when some denominator
multiplier avoids that prime. -/
theorem mem_fractionPrimeLocalAlgebra_iff (P : Ideal R) [P.IsPrime] (x : F) :
    x ∈ fractionPrimeLocalAlgebra R P ↔ ¬fractionDenominatorIdeal R x ≤ P := by
  change (∃ (a s : R) (_ : s ∈ P.primeCompl),
    x = algebraMap R F a * (algebraMap R F s)⁻¹) ↔ _
  constructor
  · rintro ⟨a, s, hs, hx⟩ hle
    have hs0 : algebraMap R F s ≠ 0 := by
      apply (map_ne_zero_iff _ (IsFractionRing.injective R F)).mpr
      intro he
      exact hs (he ▸ P.zero_mem)
    apply hs
    apply hle
    apply (mem_fractionDenominatorIdeal R x s).mpr
    refine ⟨a, ?_⟩
    rw [hx]
    field_simp
  · intro hle
    change ¬∀ s, s ∈ fractionDenominatorIdeal R x → s ∈ P at hle
    push Not at hle
    obtain ⟨s, hs, hsP⟩ := hle
    obtain ⟨a, ha⟩ := (mem_fractionDenominatorIdeal R x s).mp hs
    refine ⟨a, s, hsP, ?_⟩
    have hs0 : algebraMap R F s ≠ 0 := by
      apply (map_ne_zero_iff _ (IsFractionRing.injective R F)).mpr
      intro he
      exact hsP (he ▸ P.zero_mem)
    rw [← div_eq_mul_inv]
    apply (eq_div_iff hs0).mpr
    simpa only [mul_comm] using ha.symm

variable [IsNoetherianRing R] [IsIntegrallyClosed R]

/-- A nonregular fraction has an actual height-one localization in
which it remains nonregular. -/
theorem normal_nonregular_fraction_constructs_height_one_pole
    (x : F) (hx : ¬IsLocalization.IsInteger R x) :
    ∃ (P : Ideal R) (_hP : P.IsPrime), P.height = 1 ∧
      x ∉ fractionPrimeLocalAlgebra R P := by
  obtain ⟨P, hP, hh, hle⟩ := normal_nonregular_fraction_constructs_height_one_prime x hx
  exact ⟨P, hP, hh, fun h => (mem_fractionPrimeLocalAlgebra_iff R P x).mp h hle⟩

/-- A rational function on a normal Noetherian domain is regular
if and only if it is regular at every height-one prime. -/
theorem normal_fraction_regular_iff_height_one_localizations (x : F) :
    IsLocalization.IsInteger R x ↔
      ∀ (P : Ideal R) [P.IsPrime], P.height = 1 → x ∈ fractionPrimeLocalAlgebra R P := by
  constructor
  · rintro ⟨a, rfl⟩ P hP hh
    exact (fractionPrimeLocalAlgebra R P).algebraMap_mem a
  · intro hreg
    by_contra hx
    obtain ⟨P, hP, hh, hpole⟩ := normal_nonregular_fraction_constructs_height_one_pole R x hx
    exact hpole (hreg P hh)

end DimensionFourDependence
