import DimensionFourDependence.NormalizedPrimeFactorProducts

/-! # Uniqueness of the actual prime-exponent power decomposition -/

namespace DimensionFourDependence

open UniqueFactorizationMonoid

set_option maxHeartbeats 2000000

variable {R : Type*} [CommMonoidWithZero R] [Nontrivial R] [NormalizationMonoid R]
    [UniqueFactorizationMonoid R] [DecidableEq R]

/-- Association preserves the complete actual normalized prime-exponent function. -/
theorem factorization_eq_of_associated (a b : R) (h : Associated a b) :
    factorization a = factorization b := by
  exact congrArg Multiset.toFinsupp h.normalizedFactors_eq

/-- Any supplied presentation with a d-power-free first factor agrees,
up to units, with the internally constructed remainder and quotient. -/
theorem actual_power_remainder_quotient_unique
    (P A B : R) (d : ℕ) (hd : 0 < d)
    (hP : P ≠ 0) (hA : A ≠ 0) (hB : B ≠ 0)
    (hfactor : Associated P (A * B ^ d))
    (hsmall : ∀ p, factorization A p < d) :
    Associated (factorizationPowerRemainder P d) A ∧
      Associated (factorizationPowerQuotient P d) B := by
  have hf : factorization P = factorization A + d • factorization B := by
    rw [← factorization_pow, ← factorization_mul hA (pow_ne_zero d hB)]
    exact factorization_eq_of_associated _ _ hfactor
  have hrem0 : factorizationPowerRemainder P d ≠ 0 :=
    factorization_support_power_product_ne_zero P (fun p => factorization P p % d)
  have hquo0 : factorizationPowerQuotient P d ≠ 0 :=
    factorization_support_power_product_ne_zero P (fun p => factorization P p / d)
  constructor
  · apply associated_of_factorization_eq _ _ hrem0 hA
    ext p
    rw [factorization_power_remainder_apply, hf]
    simp only [Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul, Nat.add_mul_mod_self_left]
    exact Nat.mod_eq_of_lt (hsmall p)
  · apply associated_of_factorization_eq _ _ hquo0 hB
    ext p
    rw [factorization_power_quotient_apply, hf]
    simp only [Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul]
    rw [Nat.add_mul_div_left _ _ hd, Nat.div_eq_of_lt (hsmall p), Nat.zero_add]

end DimensionFourDependence
