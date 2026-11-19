import DimensionFourDependence.PowerRemainderUniqueness
import DimensionFourDependence.UnivariateLinearPowerDescent

/-! # The canonical power factors on a ruling have degree at most one -/

namespace DimensionFourDependence

open UniqueFactorizationMonoid

set_option maxHeartbeats 2000000

variable {K E : Type*} [Field K] [Field E]
    [NormalizationMonoid K] [DecidableEq (Polynomial K)]

/-- A nonzero affine linear polynomial has no repeated prime factor,
including the case in which the affine polynomial is a nonzero constant. -/
theorem affine_linear_polynomial_factorization_le_one
    (A : Polynomial K) (hA : A ≠ 0) (hdeg : A.natDegree ≤ 1) (p : Polynomial K) :
    factorization A p ≤ 1 := by
  classical
  by_cases hu : IsUnit A
  · rw [factorization_eq_of_associated A 1 (associated_one_iff_isUnit.mpr hu)]
    simp
  · have hdeg1 : A.natDegree = 1 := by
      by_contra h
      have hz : A.natDegree = 0 := by omega
      have hd0 : A.degree = 0 := by rw [Polynomial.degree_eq_natDegree hA, hz]; rfl
      exact hu (Polynomial.isUnit_iff_degree_eq_zero.mpr hd0)
    have hirr : Irreducible A := Polynomial.irreducible_of_degree_eq_one (by
      rw [Polynomial.degree_eq_natDegree hA, hdeg1]; rfl)
    rw [factorization_eq_count, normalizedFactors_irreducible hirr, Multiset.count_singleton]
    split_ifs <;> omega

/-- An original-field ruling presentation identifies the actual
prime-exponent factors and bounds their degrees by one. -/
theorem linear_times_power_canonical_factors_degree_le_one
    (P A B : Polynomial K) (hP : P ≠ 0) (hA : A ≠ 0) (hB : B ≠ 0)
    (hdegA : A.natDegree ≤ 1) (hdegB : B.natDegree ≤ 1)
    (d : ℕ) (hd : 1 < d) (hfactor : P = A * B ^ d) :
    (factorizationPowerRemainder P d).natDegree ≤ 1 ∧
      (factorizationPowerQuotient P d).natDegree ≤ 1 := by
  classical
  have hsmall (p : Polynomial K) : factorization A p < d :=
    (affine_linear_polynomial_factorization_le_one A hA hdegA p).trans_lt hd
  obtain ⟨hrem, hquo⟩ := actual_power_remainder_quotient_unique P A B d (by omega)
    hP hA hB (Associated.of_eq hfactor) hsmall
  have hremdeg := Polynomial.natDegree_eq_of_degree_eq (Polynomial.degree_eq_degree_of_associated hrem)
  have hquodeg := Polynomial.natDegree_eq_of_degree_eq (Polynomial.degree_eq_degree_of_associated hquo)
  exact ⟨hremdeg.le.trans hdegA, hquodeg.le.trans hdegB⟩

variable [CharZero E]

/-- Even when the actual ruling factors are first realized over an
extension, its internally constructed original-field canonical factors
have degree at most one. The factors and their descent are derived. -/
theorem extension_linear_times_power_canonical_factors_degree_le_one
    (f : K →+* E) (P : Polynomial K) (hP : P ≠ 0)
    (a b : Fin 2 → E) (d : ℕ) (hd : 1 < d)
    (hfactor : P.map f = segreRulingPowerPolynomial a b d) :
    (factorizationPowerRemainder P d).natDegree ≤ 1 ∧
      (factorizationPowerQuotient P d).natDegree ≤ 1 := by
  obtain ⟨A, B, hA, hB, hdegA, hdegB, he⟩ :=
    univariate_linear_times_power_constructs_original_linear_factors f P hP a b d hd hfactor
  exact linear_times_power_canonical_factors_degree_le_one P A B hP hA hB hdegA hdegB d hd he

end DimensionFourDependence
