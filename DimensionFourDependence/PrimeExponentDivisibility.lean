import DimensionFourDependence.NormalizedPrimeFactorProducts

/-! # Divisibility is exactly comparison of actual prime exponents -/

namespace DimensionFourDependence

open UniqueFactorizationMonoid

variable {R : Type*} [CommMonoidWithZero R] [Nontrivial R] [NormalizationMonoid R]
    [UniqueFactorizationMonoid R] [DecidableEq R]

/-- Compare the actual prime multiplicities to decide divisibility,
with the zero cases explicitly excluded. -/
theorem dvd_iff_actual_factorization_le (a b : R) (ha : a ≠ 0) (hb : b ≠ 0) :
    a ∣ b ↔ ∀ p, factorization a p ≤ factorization b p := by
  rw [dvd_iff_normalizedFactors_le_normalizedFactors ha hb, Multiset.le_iff_count]
  rfl

/-- An actual irreducible power divides exactly when its normalized
prime multiplicity is at least the indicated exponent. -/
theorem irreducible_power_dvd_iff_actual_exponent_le
    (p a : R) (hp : Irreducible p) (ha : a ≠ 0) (n : ℕ) :
    p ^ n ∣ a ↔ n ≤ factorization a (normalize p) := by
  rw [dvd_iff_actual_factorization_le _ _ (pow_ne_zero n hp.ne_zero) ha]
  simp only [factorization_pow, Finsupp.smul_apply, smul_eq_mul, factorization_eq_count,
    normalizedFactors_irreducible hp, Multiset.count_singleton]
  constructor
  · intro h
    simpa only [eq_self_iff_true, ite_true, mul_one] using h (normalize p)
  · intro h q
    by_cases hq : q = normalize p
    · subst q
      simpa only [eq_self_iff_true, ite_true, mul_one] using h
    · simp only [hq, if_false, mul_zero, Nat.zero_le]

end DimensionFourDependence
