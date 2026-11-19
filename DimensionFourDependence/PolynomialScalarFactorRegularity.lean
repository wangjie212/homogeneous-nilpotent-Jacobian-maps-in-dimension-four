import DimensionFourDependence.ValuativeIntegralCriterion
import Mathlib.RingTheory.Valuation.IsTrivialOn
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed

/-! # A polynomial scalar factor forces its source factor to be regular

If z lies in R[t] and A(t) z^d lies in R for a nonconstant polynomial
A over constant field K, then z is integral over R. A valuation containing
R but excluding z would also exclude t. Its value on A(t) is greater
than one, so the product cannot belong to R. In a normal source fraction
field this constructs z as an actual element of R.
-/

namespace DimensionFourDependence

set_option maxHeartbeats 2000000

variable {K R F : Type*} [Field K] [CommRing R] [Field F]
    [Algebra K R] [Algebra K F] [Algebra R F] [IsScalarTower K R F]

/-- A source factor polynomial in the parameter is integral if a
nonconstant constant-coefficient polynomial in that parameter times
any power of the factor is an original regular source value. -/
theorem source_factor_integral_of_nonconstant_polynomial_scalar
    (t z : F) (hz : z ∈ Algebra.adjoin R {t})
    (A : Polynomial K) (hA : 0 < A.natDegree) (d : ℕ) (H : R)
    (hH : algebraMap R F H = Polynomial.aeval t A * z ^ d) :
    IsIntegral R z := by
  apply isIntegral_of_mem_all_valuationSubrings
  intro V hR
  by_contra hzV
  have htV : t ∉ V := by
    intro ht
    let B : Subalgebra R F := { V.toSubring with algebraMap_mem' := hR }
    have hle : Algebra.adjoin R {t} ≤ B :=
      Algebra.adjoin_le (Set.singleton_subset_iff.mpr ht)
    exact hzV (hle hz)
  have hzpos : 1 < V.valuation z :=
    lt_of_not_ge (fun h => hzV ((V.valuation_le_one_iff z).mp h))
  have htpos : 1 < V.valuation t :=
    lt_of_not_ge (fun h => htV ((V.valuation_le_one_iff t).mp h))
  have hK (c : K) : V.valuation (algebraMap K F c) ≤ 1 := by
    apply (V.valuation_le_one_iff _).mpr
    rw [IsScalarTower.algebraMap_apply K R F]
    exact hR _
  let : V.valuation.IsTrivialOn K := Valuation.IsTrivialOn.of_le_one V.valuation hK
  have hA0 : A ≠ 0 := by intro h; simp [h] at hA
  have hAval : V.valuation (Polynomial.aeval t A) = V.valuation t ^ A.natDegree :=
    Polynomial.valuation_aeval_eq_valuation_X_pow_natDegree_of_one_lt_valuation_X t htpos hA0
  have hApos : 1 < V.valuation (Polynomial.aeval t A) := by
    rw [hAval]
    exact one_lt_pow₀ htpos (Nat.ne_of_gt hA)
  have hprod : 1 < V.valuation (Polynomial.aeval t A * z ^ d) := by
    rw [map_mul, map_pow]
    apply hApos.trans_le
    simpa only [mul_one] using mul_le_mul_of_nonneg_left
      (one_le_pow₀ hzpos.le) (zero_lt_one.trans hApos).le
  exact (not_lt_of_ge ((V.valuation_le_one_iff _).mpr (hR H))) (hH ▸ hprod)

/-- Normality turns the integral source factor into an actual source
polynomial or regular function, with its exact original field value. -/
theorem source_factor_regular_of_nonconstant_polynomial_scalar
    [IsDomain R] [IsIntegrallyClosed R] [IsFractionRing R F]
    (t z : F) (hz : z ∈ Algebra.adjoin R {t})
    (A : Polynomial K) (hA : 0 < A.natDegree) (d : ℕ) (H : R)
    (hH : algebraMap R F H = Polynomial.aeval t A * z ^ d) :
    ∃ Z : R, algebraMap R F Z = z :=
  IsIntegrallyClosed.algebraMap_eq_of_integral
    (source_factor_integral_of_nonconstant_polynomial_scalar t z hz A hA d H hH)

end DimensionFourDependence
