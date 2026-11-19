import DimensionFourDependence.FactorizationPowerRemainder

/-! # Exact prime multiplicities of the constructed power remainder and quotient -/

namespace DimensionFourDependence

open UniqueFactorizationMonoid

set_option maxHeartbeats 2000000

variable {R : Type*} [CommMonoidWithZero R] [Nontrivial R] [NormalizationMonoid R]
    [UniqueFactorizationMonoid R] [DecidableEq R]

/-- The actual factorization of a normalized prime has its single original entry. -/
theorem factorization_normalized_prime (p : R) (hp : Prime p) (hn : normalize p = p) :
    factorization p = Finsupp.single p 1 := by
  ext q
  simp only [factorization_eq_count, normalizedFactors_irreducible hp.irreducible, hn,
    Multiset.count_singleton, Finsupp.single_apply]
  by_cases h : p = q
  · subst q
    simp only [if_pos rfl]
  · simp only [h, Ne.symm h, if_false]

/-- A product of powers of distinct normalized primes retains exactly
the specified multiplicities, including zero multiplicities. -/
theorem factorization_normalized_prime_finset_product (s : Finset R) (e : R → ℕ)
    (hp : ∀ p ∈ s, Prime p) (hn : ∀ p ∈ s, normalize p = p) :
    factorization (∏ p ∈ s, p ^ e p) = ∑ p ∈ s, Finsupp.single p (e p) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    have hpa := hp a (Finset.mem_insert_self a s)
    have hps : ∀ p ∈ s, Prime p := fun p h => hp p (Finset.mem_insert_of_mem h)
    have hns : ∀ p ∈ s, normalize p = p := fun p h => hn p (Finset.mem_insert_of_mem h)
    have hprod : (∏ p ∈ s, p ^ e p) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr (fun p h => pow_ne_zero _ (hps p h).ne_zero)
    rw [Finset.prod_insert ha, factorization_mul (pow_ne_zero _ hpa.ne_zero) hprod,
      factorization_pow, factorization_normalized_prime a hpa (hn a (Finset.mem_insert_self a s)),
      ih hps hns, Finset.sum_insert ha]
    simp

/-- Every actual prime-support power product has exactly the original
support exponents after the indicated transformation. -/
theorem factorization_original_support_power_product (P : R) (e : ℕ → ℕ) (he : e 0 = 0) :
    factorization ((factorization P).prod (fun p n => p ^ e n)) =
      (factorization P).mapRange e he := by
  have hp : ∀ p ∈ (factorization P).support, Prime p := by
    intro p h
    exact prime_of_normalized_factor p (by
      simpa only [support_factorization, Multiset.mem_toFinset] using h)
  have hn : ∀ p ∈ (factorization P).support, normalize p = p := by
    intro p h
    exact normalize_normalized_factor p (by
      simpa only [support_factorization, Multiset.mem_toFinset] using h)
  rw [Finsupp.prod, factorization_normalized_prime_finset_product _ _ hp hn]
  ext q
  by_cases hq : q ∈ (factorization P).support
  · simp only [Finsupp.finsetSum_apply, Finsupp.mapRange_apply, Finsupp.single_apply]
    rw [Finset.sum_eq_single q]
    · simp
    · intro b _hb hbq
      simp [hbq]
    · exact fun h => False.elim (h hq)
  · have hq0 : factorization P q = 0 := Finsupp.notMem_support_iff.mp hq
    simp only [Finsupp.finsetSum_apply, Finsupp.mapRange_apply, hq0, he]
    apply Finset.sum_eq_zero
    intro b hb
    have hbq : b ≠ q := by intro h; subst b; exact hq hb
    simp [Finsupp.single_apply, hbq]

/-- The remainder's actual prime multiplicity is the original multiplicity modulo d. -/
theorem factorization_power_remainder_apply (P p : R) (d : ℕ) :
    factorization (factorizationPowerRemainder P d) p = factorization P p % d := by
  have h := factorization_original_support_power_product P (fun n => n % d) (Nat.zero_mod d)
  exact congrArg (fun a : R →₀ ℕ => a p) h

/-- The quotient's actual prime multiplicity is the original multiplicity divided by d. -/
theorem factorization_power_quotient_apply (P p : R) (d : ℕ) :
    factorization (factorizationPowerQuotient P d) p = factorization P p / d := by
  have h := factorization_original_support_power_product P (fun n => n / d) (Nat.zero_div d)
  exact congrArg (fun a : R →₀ ℕ => a p) h

/-- The constructed remainder is d-power-free at every actual prime. -/
theorem factorization_power_remainder_exponent_lt (P p : R) (d : ℕ) (hd : 0 < d) :
    factorization (factorizationPowerRemainder P d) p < d := by
  rw [factorization_power_remainder_apply]
  exact Nat.mod_lt _ hd

end DimensionFourDependence
