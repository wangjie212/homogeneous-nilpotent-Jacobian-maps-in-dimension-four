import DimensionFourDependence.Defs
import Mathlib.RingTheory.UniqueFactorizationDomain.Finsupp

/-! # Actual prime-exponent remainder and power quotient in a unique factorization domain -/

namespace DimensionFourDependence

open UniqueFactorizationMonoid

set_option maxHeartbeats 1500000

variable {R : Type*} [CommMonoidWithZero R] [Nontrivial R] [NormalizationMonoid R]
    [UniqueFactorizationMonoid R] [DecidableEq R]

/-- Reduce every actual normalized prime exponent modulo the specified power. -/
noncomputable def factorizationPowerRemainder (P : R) (d : ℕ) : R :=
  (factorization P).prod (fun p n => p ^ (n % d))

/-- Divide every actual normalized prime exponent by the specified power. -/
noncomputable def factorizationPowerQuotient (P : R) (d : ℕ) : R :=
  (factorization P).prod (fun p n => p ^ (n / d))

/-- The actual prime-exponent product is the original normalized factor product. -/
theorem factorization_prime_power_product_eq_normalized_product (P : R) :
    (factorization P).prod (fun p n => p ^ n) = (normalizedFactors P).prod := by
  simp only [Finsupp.prod, support_factorization, factorization_eq_count]
  exact (Finset.prod_multiset_count (normalizedFactors P)).symm

/-- Any product of powers over the original actual normalized prime
support is nonzero, including zero exponents and an empty support. -/
theorem factorization_support_power_product_ne_zero (P : R) (e : R → ℕ) :
    (factorization P).prod (fun p _ => p ^ e p) ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro p hp
  have hm : p ∈ normalizedFactors P := by
    simpa only [support_factorization, Multiset.mem_toFinset] using hp
  exact pow_ne_zero _ (prime_of_normalized_factor p hm).ne_zero

/-- The constructed actual remainder and quotient exactly reconstruct
the original normalized factor product, without supplied divisor data. -/
theorem factorization_power_remainder_quotient_product (P : R) (d : ℕ) :
    factorizationPowerRemainder P d * factorizationPowerQuotient P d ^ d =
      (normalizedFactors P).prod := by
  rw [← factorization_prime_power_product_eq_normalized_product]
  simp only [factorizationPowerRemainder, factorizationPowerQuotient, Finsupp.prod]
  rw [← Finset.prod_pow, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro p _hp
  rw [← pow_mul, ← pow_add]
  congr 1
  simpa only [Nat.mul_comm] using Nat.mod_add_div (factorization P p) d

/-- Every nonzero original element is associated to its actual prime
remainder times the dth power of its actual prime quotient. -/
theorem factorization_power_remainder_quotient_associated (P : R) (hP : P ≠ 0) (d : ℕ) :
    Associated P (factorizationPowerRemainder P d * factorizationPowerQuotient P d ^ d) := by
  have he := prod_normalizedFactors hP
  rw [← factorization_power_remainder_quotient_product P d] at he
  exact he.symm

/-- The actual prime multiplicities construct an exact power
factorization with its original unit, rather than an assumed divisor decomposition. -/
theorem factorization_power_remainder_quotient_exact (P : R) (hP : P ≠ 0) (d : ℕ) :
    ∃ u : Rˣ, P = (u : R) * factorizationPowerRemainder P d * factorizationPowerQuotient P d ^ d := by
  obtain ⟨u, hu⟩ := (factorization_power_remainder_quotient_associated P hP d).symm
  refine ⟨u, ?_⟩
  calc
    P = (factorizationPowerRemainder P d * factorizationPowerQuotient P d ^ d) * (u : R) := hu.symm
    _ = _ := by ac_rfl

end DimensionFourDependence
