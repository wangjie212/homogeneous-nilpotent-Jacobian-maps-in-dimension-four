import DimensionFourDependence.PrincipalVanishingDivisor
import DimensionFourDependence.PencilBaseZeroBranch

/-! # A separating prime constructs actual height-one zero and denominator branches -/

namespace DimensionFourDependence

variable {R B F : Type*} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [CommRing B] [IsLocalRing B] [Field F] [Algebra R F] [IsFractionRing R F]

/-- A prime containing a nonzero numerator and avoiding the
denominator constructs a height-one zero branch with the same avoidance. -/
theorem separating_prime_constructs_height_one_zero_germ
    (n l : R) (hn : n ≠ 0) (P : Ideal R) [P.IsPrime]
    (hnP : n ∈ P) (hlP : l ∉ P) (d : ℕ) :
    ∃ q : PrimeSpectrum R, q.asIdeal.height = 1 ∧ q.asIdeal ≤ P ∧
      n ∈ q.asIdeal ∧ l ∉ q.asIdeal ∧
      ∃ g : fractionPrimeLocalAlgebra (F := F) R q.asIdeal,
        (g : F) = algebraMap R F n / (algebraMap R F l) ^ d ∧
        g ∈ IsLocalRing.maximalIdeal (fractionPrimeLocalAlgebra (F := F) R q.asIdeal) := by
  obtain ⟨q, hq, hnq, hqP⟩ := nonzero_function_prime_contains_vanishing_divisor n hn P hnP
  have hlq : l ∉ q.asIdeal := fun h => hlP (hqP h)
  exact ⟨q, hq, hqP, hnq, hlq,
    quotient_constructs_vanishing_prime_local_germ q.asIdeal n l hnq hlq d⟩

/-- A specified specialization-like ring map supplies the separating
prime from its actual numerator and denominator germs. -/
theorem local_map_constructs_height_one_zero_germ
    (φ : R →+* B) (n l : R) (hn : n ≠ 0)
    (hnφ : φ n ∈ IsLocalRing.maximalIdeal B) (hlφ : IsUnit (φ l)) (d : ℕ) :
    ∃ q : PrimeSpectrum R, q.asIdeal.height = 1 ∧ n ∈ q.asIdeal ∧ l ∉ q.asIdeal ∧
      ∃ g : fractionPrimeLocalAlgebra (F := F) R q.asIdeal,
        (g : F) = algebraMap R F n / (algebraMap R F l) ^ d ∧
        g ∈ IsLocalRing.maximalIdeal (fractionPrimeLocalAlgebra (F := F) R q.asIdeal) := by
  let P := (IsLocalRing.maximalIdeal B).comap φ
  let : P.IsPrime := Ideal.comap_isPrime φ _
  have hlP : l ∉ P := IsLocalRing.notMem_maximalIdeal.mpr hlφ
  obtain ⟨q, hq, hqP, hnq, hlq, hg⟩ :=
    separating_prime_constructs_height_one_zero_germ (F := F) n l hn P hnφ hlP d
  exact ⟨q, hq, hnq, hlq, hg⟩

variable [IsLocalRing R]

/-- A denominator zero in the original local ring and a separating
specialization construct two distinct height-one branches through its
closed point, with an actual vanishing quotient germ on the first. -/
theorem local_map_constructs_distinct_zero_and_denominator_divisors
    (φ : R →+* B) (n l : R) (hn : n ≠ 0)
    (hnφ : φ n ∈ IsLocalRing.maximalIdeal B) (hlφ : IsUnit (φ l))
    (hl : l ∈ IsLocalRing.maximalIdeal R) (d : ℕ) :
    ∃ q₀ qL : PrimeSpectrum R,
      q₀.asIdeal.height = 1 ∧ qL.asIdeal.height = 1 ∧ q₀ ≠ qL ∧
      n ∈ q₀.asIdeal ∧ l ∉ q₀.asIdeal ∧ l ∈ qL.asIdeal ∧
      ∃ g : fractionPrimeLocalAlgebra (F := F) R q₀.asIdeal,
        (g : F) = algebraMap R F n / (algebraMap R F l) ^ d ∧
        g ∈ IsLocalRing.maximalIdeal (fractionPrimeLocalAlgebra (F := F) R q₀.asIdeal) := by
  obtain ⟨q₀, hq₀, hnq₀, hlq₀, hg⟩ := local_map_constructs_height_one_zero_germ
    (F := F) φ n l hn hnφ hlφ d
  have hl0 : l ≠ 0 := by
    intro he
    have hu : IsUnit (0 : B) := by simpa only [he, map_zero] using hlφ
    exact not_isUnit_zero hu
  obtain ⟨qL, hqL, hlqL⟩ := nonzero_nonunit_function_has_vanishing_divisor l hl0 hl
  have hne : q₀ ≠ qL := by
    intro he
    exact hlq₀ (he ▸ hlqL)
  exact ⟨q₀, qL, hq₀, hqL, hne, hnq₀, hlq₀, hlqL, hg⟩

end DimensionFourDependence
