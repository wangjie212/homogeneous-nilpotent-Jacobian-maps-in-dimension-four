import DimensionFourDependence.FractionPolynomialCanonicalFactors
import DimensionFourDependence.UnivariateScalarLinearPowerDescent

/-! # A pure linear power has constant canonical remainder -/

namespace DimensionFourDependence

open Polynomial UniqueFactorizationMonoid

set_option maxHeartbeats 3000000

variable {K : Type*} [Field K] [NormalizationMonoid K] [DecidableEq (Polynomial K)]

/-- An exact scalar times a linear power forces the actual canonical
remainder to be constant, while the canonical quotient remains linear. -/
theorem scalar_linear_power_canonical_factors_degree_bounds
    (P : Polynomial K) (hP : P ≠ 0) (α : K) (hα : α ≠ 0)
    (B : Polynomial K) (hB : B ≠ 0) (hdegB : B.natDegree ≤ 1)
    (d : ℕ) (hd : 0 < d) (hfactor : P = Polynomial.C α * B ^ d) :
    (factorizationPowerRemainder P d).natDegree = 0 ∧
      (factorizationPowerQuotient P d).natDegree ≤ 1 := by
  classical
  have hunit : IsUnit (Polynomial.C α) := (isUnit_iff_ne_zero.mpr hα).map Polynomial.C
  have hsmall (p : Polynomial K) : factorization (Polynomial.C α) p < d := by
    rw [factorization_eq_of_associated _ 1 (associated_one_iff_isUnit.mpr hunit)]
    simpa using hd
  obtain ⟨hrem, hquo⟩ := actual_power_remainder_quotient_unique P (Polynomial.C α) B d hd
    hP (Polynomial.C_ne_zero.mpr hα) hB (Associated.of_eq hfactor) hsmall
  have hremdeg := Polynomial.natDegree_eq_of_degree_eq (Polynomial.degree_eq_degree_of_associated hrem)
  have hquodeg := Polynomial.natDegree_eq_of_degree_eq (Polynomial.degree_eq_degree_of_associated hquo)
  exact ⟨hremdeg.trans (Polynomial.natDegree_C α), hquodeg.le.trans hdegB⟩

variable {R F : Type*} [CommRing R] [IsDomain R] [NormalizedGCDMonoid R]
    [UniqueFactorizationMonoid R] [Field F] [Algebra R F] [IsFractionRing R F]
    [NormalizationMonoid F] [DecidableEq (Polynomial R)] [DecidableEq (Polynomial F)]

/-- Localization cannot hide positive degree in the original canonical
remainder. The scalar-linear-power presentation therefore gives the
same constant/linear bounds over the original coefficient domain. -/
theorem fraction_scalar_linear_power_original_canonical_degree_bounds
    (P : Polynomial R) (hP : P ≠ 0) (α : F) (hα : α ≠ 0)
    (B : Polynomial F) (hB : B ≠ 0) (hdegB : B.natDegree ≤ 1)
    (d : ℕ) (hd : 0 < d)
    (hfactor : P.map (algebraMap R F) = Polynomial.C α * B ^ d) :
    (factorizationPowerRemainder P d).natDegree = 0 ∧
      (factorizationPowerQuotient P d).natDegree ≤ 1 := by
  classical
  have hmap0 : P.map (algebraMap R F) ≠ 0 := by
    intro hz
    apply hP
    apply Polynomial.map_injective _ (IsFractionRing.injective R F)
    simpa only [Polynomial.map_zero] using hz
  obtain ⟨hr, hq⟩ := scalar_linear_power_canonical_factors_degree_bounds
    _ hmap0 α hα B hB hdegB d hd hfactor
  obtain ⟨hrem, hquo⟩ := fraction_polynomial_canonical_factors_associated (F := F) P hP d hd
  have hremmap := Polynomial.natDegree_eq_of_degree_eq (Polynomial.degree_eq_degree_of_associated hrem)
  have hquomap := Polynomial.natDegree_eq_of_degree_eq (Polynomial.degree_eq_degree_of_associated hquo)
  rw [Polynomial.natDegree_map_eq_of_injective (IsFractionRing.injective R F)] at hremmap hquomap
  exact ⟨hremmap.symm.trans hr, hquomap.symm.le.trans hq⟩

end DimensionFourDependence
