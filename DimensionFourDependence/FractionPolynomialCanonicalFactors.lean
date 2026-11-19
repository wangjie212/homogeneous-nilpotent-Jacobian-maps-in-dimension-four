import DimensionFourDependence.FractionPolynomialPowerFree
import DimensionFourDependence.LinearPolynomialPowerRemainder

/-! # Canonical power factors and their degrees over a coefficient fraction field -/

namespace DimensionFourDependence

open Polynomial UniqueFactorizationMonoid

set_option maxHeartbeats 2500000

variable {R F : Type*} [CommRing R] [IsDomain R] [NormalizedGCDMonoid R]
    [UniqueFactorizationMonoid R] [Field F] [Algebra R F] [IsFractionRing R F]
    [NormalizationMonoid F] [DecidableEq (Polynomial R)] [DecidableEq (Polynomial F)]

/-- The actual original prime-exponent factors map to the actual
fraction-field prime-exponent factors, up to their unavoidable units. -/
theorem fraction_polynomial_canonical_factors_associated
    (P : Polynomial R) (hP : P ≠ 0) (d : ℕ) (hd : 0 < d) :
    Associated (factorizationPowerRemainder (P.map (algebraMap R F)) d)
        ((factorizationPowerRemainder P d).map (algebraMap R F)) ∧
      Associated (factorizationPowerQuotient (P.map (algebraMap R F)) d)
        ((factorizationPowerQuotient P d).map (algebraMap R F)) := by
  classical
  have hmap0 (Q : Polynomial R) (hQ : Q ≠ 0) : Q.map (algebraMap R F) ≠ 0 := by
    intro h
    apply hQ
    apply Polynomial.map_injective _ (IsFractionRing.injective R F)
    simpa only [Polynomial.map_zero] using h
  have hrem0 : factorizationPowerRemainder P d ≠ 0 :=
    factorization_support_power_product_ne_zero P (fun p => factorization P p % d)
  have hquo0 : factorizationPowerQuotient P d ≠ 0 :=
    factorization_support_power_product_ne_zero P (fun p => factorization P p / d)
  have hfactor : Associated (P.map (algebraMap R F))
      (((factorizationPowerRemainder P d).map (algebraMap R F)) *
        ((factorizationPowerQuotient P d).map (algebraMap R F)) ^ d) := by
    simpa only [Polynomial.map_mul, Polynomial.map_pow] using
      Polynomial.associated_map_map (algebraMap R F)
        (factorization_power_remainder_quotient_associated P hP d)
  exact actual_power_remainder_quotient_unique _ _ _ d hd (hmap0 P hP)
    (hmap0 _ hrem0) (hmap0 _ hquo0) hfactor
    (fraction_polynomial_constructed_remainder_power_free P d hd)

/-- An actual linear-times-power identity over the coefficient fraction
field bounds the original canonical factors' degrees, without assuming
a factorization over the coefficient domain. -/
theorem fraction_linear_times_power_original_canonical_degree_le_one
    (P : Polynomial R) (hP : P ≠ 0) (A B : Polynomial F)
    (hA : A ≠ 0) (hB : B ≠ 0) (hdegA : A.natDegree ≤ 1) (hdegB : B.natDegree ≤ 1)
    (d : ℕ) (hd : 1 < d) (hfactor : P.map (algebraMap R F) = A * B ^ d) :
    (factorizationPowerRemainder P d).natDegree ≤ 1 ∧
      (factorizationPowerQuotient P d).natDegree ≤ 1 := by
  classical
  have hmap0 : P.map (algebraMap R F) ≠ 0 := by
    intro h
    apply hP
    apply Polynomial.map_injective _ (IsFractionRing.injective R F)
    simpa only [Polynomial.map_zero] using h
  obtain ⟨hremdeg, hquodeg⟩ := linear_times_power_canonical_factors_degree_le_one
    _ A B hmap0 hA hB hdegA hdegB d hd hfactor
  obtain ⟨hrem, hquo⟩ := fraction_polynomial_canonical_factors_associated (F := F) P hP d (by omega)
  have hremmap := Polynomial.natDegree_eq_of_degree_eq (Polynomial.degree_eq_degree_of_associated hrem)
  have hquomap := Polynomial.natDegree_eq_of_degree_eq (Polynomial.degree_eq_degree_of_associated hquo)
  rw [Polynomial.natDegree_map_eq_of_injective (IsFractionRing.injective R F)] at hremmap hquomap
  exact ⟨hremmap.symm.le.trans hremdeg, hquomap.symm.le.trans hquodeg⟩

end DimensionFourDependence
