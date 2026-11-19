import DimensionFourDependence.NormalizationRing
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem

/-! # Nonzero regular functions have a divisor through every zero -/

namespace DimensionFourDependence

variable {R : Type*} [CommRing R] [IsDomain R] [IsNoetherianRing R]

/-- Every prime containing a nonzero regular function contains an
actual height-one prime of that function's zero locus. -/
theorem nonzero_function_prime_contains_vanishing_divisor
    (x : R) (hx : x ≠ 0) (P : Ideal R) [P.IsPrime] (hxP : x ∈ P) :
    ∃ q : PrimeSpectrum R, q.asIdeal.height = 1 ∧ x ∈ q.asIdeal ∧ q.asIdeal ≤ P := by
  have hspan : Ideal.span ({x} : Set R) ≤ P := Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hxP)
  obtain ⟨Q, hQ, hQP⟩ := Ideal.exists_minimalPrimes_le hspan
  let : Q.IsPrime := hQ.isPrime
  have hxQ : x ∈ Q := hQ.le (Ideal.subset_span (Set.mem_singleton x))
  have hne : Q ≠ ⊥ := by
    intro hzero
    exact hx (by simpa only [hzero, Ideal.mem_bot] using hxQ)
  have hh : Q.height = 1 := le_antisymm
    (Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes (Ideal.span {x}) Q hQ)
    (Order.one_le_iff_ne_zero.mpr (mt Ideal.height_eq_zero_iff_eq_bot.mp hne))
  exact ⟨⟨Q, inferInstance⟩, hh, hxQ, hQP⟩

/-- A nonzero nonunit has a genuine vanishing divisor, without a
given divisor prime or a multiplicity assumption. -/
theorem nonzero_nonunit_function_has_vanishing_divisor
    (x : R) (hx : x ≠ 0) (hu : ¬ IsUnit x) :
    ∃ q : PrimeSpectrum R, q.asIdeal.height = 1 ∧ x ∈ q.asIdeal := by
  obtain ⟨P, hP, hle⟩ := Ideal.exists_le_maximal (Ideal.span {x}) (by simpa using hu)
  let : P.IsMaximal := hP
  obtain ⟨q, hq, hxq, _⟩ := nonzero_function_prime_contains_vanishing_divisor x hx P
    (hle (Ideal.subset_span (Set.mem_singleton x)))
  exact ⟨q, hq, hxq⟩

/-- For a nonzero function, absence of divisor zeros is exactly
invertibility in the actual regular ring. -/
theorem nonzero_function_isUnit_iff_no_vanishing_divisor
    (x : R) (hx : x ≠ 0) :
    IsUnit x ↔ ∀ q : PrimeSpectrum R, q.asIdeal.height = 1 → x ∉ q.asIdeal := by
  constructor
  · intro hu q _ hxq
    exact q.isPrime.ne_top (q.asIdeal.eq_top_of_isUnit_mem hxq hu)
  · intro h
    by_contra hu
    obtain ⟨q, hq, hxq⟩ := nonzero_nonunit_function_has_vanishing_divisor x hx hu
    exact h q hq hxq

end DimensionFourDependence
