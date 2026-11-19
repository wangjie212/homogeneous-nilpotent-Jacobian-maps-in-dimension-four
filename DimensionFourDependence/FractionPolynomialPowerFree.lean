import DimensionFourDependence.FractionPolynomialPrimeLift
import DimensionFourDependence.PrimeExponentDivisibility

/-! # Actual power-free multiplicities survive passage to the coefficient fraction field -/

namespace DimensionFourDependence

open Polynomial UniqueFactorizationMonoid

set_option maxHeartbeats 2000000

variable {R F : Type*} [CommRing R] [IsDomain R] [NormalizedGCDMonoid R]
    [UniqueFactorizationMonoid R] [Field F] [Algebra R F] [IsFractionRing R F]
    [NormalizationMonoid F] [DecidableEq (Polynomial R)] [DecidableEq (Polynomial F)]

/-- A nonzero coefficient-domain polynomial with all actual prime
exponents below d retains that property over the coefficient fraction
field. Every possible fraction-field prime is lifted internally, and
Gauss's lemma reflects its power divisibility. -/
theorem fraction_polynomial_actual_power_free
    (P : Polynomial R) (hP : P ≠ 0) (d : ℕ) (hd : 0 < d)
    (hsmall : ∀ p, factorization P p < d) :
    ∀ q, factorization (P.map (algebraMap R F)) q < d := by
  classical
  have hmap0 : P.map (algebraMap R F) ≠ 0 := by
    intro h
    apply hP
    apply Polynomial.map_injective _ (IsFractionRing.injective R F)
    simpa only [Polynomial.map_zero] using h
  intro q
  by_cases hq : q ∈ (factorization (P.map (algebraMap R F))).support
  · have hqmem : q ∈ normalizedFactors (P.map (algebraMap R F)) := by
      simpa only [support_factorization, Multiset.mem_toFinset] using hq
    have hqirr : Irreducible q := (prime_of_normalized_factor q hqmem).irreducible
    have hqnorm : normalize q = q := normalize_normalized_factor q hqmem
    obtain ⟨Q, hprim, hQirr, hQmap⟩ :=
      fraction_polynomial_irreducible_constructs_primitive_prime (R := R) q hqirr
    by_contra h
    have hlarge : d ≤ factorization (P.map (algebraMap R F)) (normalize q) := by
      rw [hqnorm]
      omega
    have hqdiv : q ^ d ∣ P.map (algebraMap R F) :=
      (irreducible_power_dvd_iff_actual_exponent_le q _ hqirr hmap0 d).mpr hlarge
    have hQdivmap : (Q ^ d).map (algebraMap R F) ∣ P.map (algebraMap R F) := by
      rw [Polynomial.map_pow]
      exact hQmap.pow_pow.dvd.trans hqdiv
    have hQdiv : Q ^ d ∣ P :=
      (primitive_polynomial_power Q hprim d).dvd_of_fraction_map_dvd_fraction_map hQdivmap
    have hlargeQ := (irreducible_power_dvd_iff_actual_exponent_le Q P hQirr hP d).mp hQdiv
    exact (not_le_of_gt (hsmall (normalize Q))) hlargeQ
  · rw [Finsupp.notMem_support_iff.mp hq]
    exact hd

/-- In particular the actual constructed power remainder remains
d-power-free over the original coefficient fraction field. -/
theorem fraction_polynomial_constructed_remainder_power_free
    (P : Polynomial R) (d : ℕ) (hd : 0 < d) :
    ∀ q, factorization ((factorizationPowerRemainder P d).map (algebraMap R F)) q < d := by
  apply fraction_polynomial_actual_power_free _
    (factorization_support_power_product_ne_zero P (fun p => factorization P p % d)) d hd
  intro p
  exact factorization_power_remainder_exponent_lt P p d hd

end DimensionFourDependence
