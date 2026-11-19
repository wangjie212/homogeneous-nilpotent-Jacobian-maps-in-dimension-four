import DimensionFourDependence.PowerRemainderUniqueness
import DimensionFourDependence.PrimeExponentDivisibility

/-! # Canonical prime power factors commute with an original ring equivalence -/

namespace DimensionFourDependence

open UniqueFactorizationMonoid

set_option maxHeartbeats 2500000

variable {R S : Type*} [CommRing R] [IsDomain R] [NormalizationMonoid R]
    [UniqueFactorizationMonoid R] [DecidableEq R]
    [CommRing S] [IsDomain S] [NormalizationMonoid S]
    [UniqueFactorizationMonoid S] [DecidableEq S]

/-- Power-freeness is preserved by an arbitrary ring equivalence,
independently of the normalization choices on the two rings. -/
theorem ring_equiv_actual_power_free (e : R ≃+* S) (P : R) (hP : P ≠ 0)
    (d : ℕ) (hd : 0 < d) (hsmall : ∀ p, factorization P p < d) :
    ∀ q, factorization (e P) q < d := by
  have heP : e P ≠ 0 := by
    intro h
    apply hP
    apply e.injective
    simpa only [map_zero] using h
  intro q
  by_cases hq : q ∈ (factorization (e P)).support
  · have hmem : q ∈ normalizedFactors (e P) := by
      simpa only [support_factorization, Multiset.mem_toFinset] using hq
    have hqirr : Irreducible q := (prime_of_normalized_factor q hmem).irreducible
    have hqnorm : normalize q = q := normalize_normalized_factor q hmem
    have hpirr : Irreducible (e.symm q) :=
      (MulEquiv.irreducible_iff (f := e.symm)).mpr hqirr
    by_contra h
    have hlarge : d ≤ factorization (e P) (normalize q) := by rw [hqnorm]; omega
    have hdiv : q ^ d ∣ e P :=
      (irreducible_power_dvd_iff_actual_exponent_le q _ hqirr heP d).mpr hlarge
    have hdiv' : (e.symm q) ^ d ∣ P := by
      have hm := map_dvd e.symm.toMonoidHom hdiv
      change e.symm (q ^ d) ∣ e.symm (e P) at hm
      simpa only [map_pow, e.symm_apply_apply] using hm
    have hlarge' :=
      (irreducible_power_dvd_iff_actual_exponent_le _ _ hpirr hP d).mp hdiv'
    exact (not_le_of_gt (hsmall (normalize (e.symm q)))) hlarge'
  · rw [Finsupp.notMem_support_iff.mp hq]
    exact hd

/-- The actual prime remainder and quotient are intrinsic up to units
under a ring equivalence. This applies to exchanging the two rulings. -/
theorem ring_equiv_canonical_power_factors_associated
    (e : R ≃+* S) (P : R) (hP : P ≠ 0) (d : ℕ) (hd : 0 < d) :
    Associated (factorizationPowerRemainder (e P) d) (e (factorizationPowerRemainder P d)) ∧
      Associated (factorizationPowerQuotient (e P) d) (e (factorizationPowerQuotient P d)) := by
  have hrem0 : factorizationPowerRemainder P d ≠ 0 :=
    factorization_support_power_product_ne_zero P (fun p => factorization P p % d)
  have hquo0 : factorizationPowerQuotient P d ≠ 0 :=
    factorization_support_power_product_ne_zero P (fun p => factorization P p / d)
  have he0 (a : R) (ha : a ≠ 0) : e a ≠ 0 := by
    intro h
    apply ha
    apply e.injective
    simpa only [map_zero] using h
  have hfactor : Associated (e P)
      (e (factorizationPowerRemainder P d) * e (factorizationPowerQuotient P d) ^ d) := by
    have hm := (factorization_power_remainder_quotient_associated P hP d).map e.toMonoidHom
    change Associated (e P) (e (factorizationPowerRemainder P d * factorizationPowerQuotient P d ^ d)) at hm
    simpa only [map_mul, map_pow] using hm
  exact actual_power_remainder_quotient_unique _ _ _ d hd (he0 P hP)
    (he0 _ hrem0) (he0 _ hquo0) hfactor
    (ring_equiv_actual_power_free e _ hrem0 d hd
      (fun p => factorization_power_remainder_exponent_lt P p d hd))

end DimensionFourDependence
