import DimensionFourDependence.FractionPolynomialCanonicalFactors
import DimensionFourDependence.EquivPowerCanonicalFactors
import Mathlib.Algebra.Polynomial.Bivariate

/-! # Two rational ruling presentations construct one global bilinear power factorization -/

namespace DimensionFourDependence

open Polynomial

set_option maxHeartbeats 3000000

variable {K F : Type*} [Field K] [NormalizedGCDMonoid K]
    [Field F] [Algebra (Polynomial K) F] [IsFractionRing (Polynomial K) F]
    [NormalizationMonoid F]
    [DecidableEq (Polynomial (Polynomial K))] [DecidableEq (Polynomial F)]

/-- Degree at most one in each of the two original affine coordinates. -/
def BivariateBilinear (P : Polynomial (Polynomial K)) : Prop :=
  P.natDegree ≤ 1 ∧ (Polynomial.Bivariate.swap P).natDegree ≤ 1

/-- Both actual rational ruling presentations bound the two degrees
of the very same original prime-exponent remainder and quotient. -/
theorem two_fraction_ruling_presentations_bound_original_canonical_factors
    (P : Polynomial (Polynomial K)) (hP : P ≠ 0) (d : ℕ) (hd : 1 < d)
    (A B C D : Polynomial F)
    (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0) (hD : D ≠ 0)
    (hdegA : A.natDegree ≤ 1) (hdegB : B.natDegree ≤ 1)
    (hdegC : C.natDegree ≤ 1) (hdegD : D.natDegree ≤ 1)
    (hfirst : P.map (algebraMap (Polynomial K) F) = A * B ^ d)
    (hsecond : (Polynomial.Bivariate.swap P).map (algebraMap (Polynomial K) F) = C * D ^ d) :
    BivariateBilinear (factorizationPowerRemainder P d) ∧
      BivariateBilinear (factorizationPowerQuotient P d) := by
  classical
  have hswap0 : Polynomial.Bivariate.swap P ≠ 0 := by
    intro h
    apply hP
    apply Polynomial.Bivariate.swap.injective
    simpa only [map_zero] using h
  obtain ⟨hr1, hq1⟩ := fraction_linear_times_power_original_canonical_degree_le_one
    P hP A B hA hB hdegA hdegB d hd hfirst
  obtain ⟨hr2, hq2⟩ := fraction_linear_times_power_original_canonical_degree_le_one
    (Polynomial.Bivariate.swap P) hswap0 C D hC hD hdegC hdegD d hd hsecond
  obtain ⟨hrswap, hqswap⟩ := ring_equiv_canonical_power_factors_associated
    (Polynomial.Bivariate.swap (R := K)).toRingEquiv P hP d (by omega)
  have hrdeg := Polynomial.natDegree_eq_of_degree_eq (Polynomial.degree_eq_degree_of_associated hrswap)
  have hqdeg := Polynomial.natDegree_eq_of_degree_eq (Polynomial.degree_eq_degree_of_associated hqswap)
  exact ⟨⟨hr1, hrdeg.symm.le.trans hr2⟩, ⟨hq1, hqdeg.symm.le.trans hq2⟩⟩

/-- Two actual rational ruling identities construct global original
bilinear factors. The original nonzero polynomial is exactly R times
B to the dth power, with the unit absorbed into R. No global divisor
decomposition or compatibility of the separately chosen ruling factors
is supplied. -/
theorem two_fraction_ruling_presentations_construct_global_bilinear_power_factorization
    (P : Polynomial (Polynomial K)) (hP : P ≠ 0) (d : ℕ) (hd : 1 < d)
    (A B C D : Polynomial F)
    (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0) (hD : D ≠ 0)
    (hdegA : A.natDegree ≤ 1) (hdegB : B.natDegree ≤ 1)
    (hdegC : C.natDegree ≤ 1) (hdegD : D.natDegree ≤ 1)
    (hfirst : P.map (algebraMap (Polynomial K) F) = A * B ^ d)
    (hsecond : (Polynomial.Bivariate.swap P).map (algebraMap (Polynomial K) F) = C * D ^ d) :
    ∃ R B : Polynomial (Polynomial K), R ≠ 0 ∧ B ≠ 0 ∧
      BivariateBilinear R ∧ BivariateBilinear B ∧ P = R * B ^ d := by
  classical
  obtain ⟨hr, hq⟩ := two_fraction_ruling_presentations_bound_original_canonical_factors
    P hP d hd A B C D hA hB hC hD hdegA hdegB hdegC hdegD hfirst hsecond
  obtain ⟨u, hu⟩ := factorization_power_remainder_quotient_exact P hP d
  have hrem0 : factorizationPowerRemainder P d ≠ 0 :=
    factorization_support_power_product_ne_zero P (fun p => factorization P p % d)
  have hquo0 : factorizationPowerQuotient P d ≠ 0 :=
    factorization_support_power_product_ne_zero P (fun p => factorization P p / d)
  refine ⟨(u : Polynomial (Polynomial K)) * factorizationPowerRemainder P d,
    factorizationPowerQuotient P d, mul_ne_zero (Units.ne_zero u) hrem0, hquo0, ?_, hq, hu⟩
  constructor
  · exact Polynomial.natDegree_mul_le.trans (by
      rw [Polynomial.natDegree_eq_zero_of_isUnit (Units.isUnit u), Nat.zero_add]
      exact hr.1)
  · rw [map_mul]
    have huswap := (Units.isUnit u).map (Polynomial.Bivariate.swap (R := K)).toRingHom
    change IsUnit (Polynomial.Bivariate.swap (u : Polynomial (Polynomial K))) at huswap
    exact Polynomial.natDegree_mul_le.trans (by
      rw [Polynomial.natDegree_eq_zero_of_isUnit huswap, Nat.zero_add]
      exact hr.2)

end DimensionFourDependence
