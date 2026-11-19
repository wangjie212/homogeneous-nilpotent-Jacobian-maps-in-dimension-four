import DimensionFourDependence.RationalParameterDerivation
import DimensionFourDependence.ConstantField

/-! # The exact constant field of the rational parameter derivative

The coprime numerator and denominator of an actual rational function
have zero Wronskian when its derivative vanishes. Their polynomial
derivatives then vanish separately. Characteristic zero makes both
polynomials constant, so the actual rational function is an original scalar.
-/

namespace DimensionFourDependence

variable {K : Type*} [Field K] [CharZero K]

/-- The actual rational parameter derivative kills exactly the
original-field scalar rational functions. -/
theorem rationalParameterDerivative_eq_zero_iff_scalar (r : RatFunc K) :
    rationalParameterDerivative K r = 0 ↔ ∃ c : K, r = algebraMap K (RatFunc K) c := by
  constructor
  · intro hr
    have hdF : algebraMap (Polynomial K) (RatFunc K) r.denom ≠ 0 := by
      simpa only [map_zero] using
        (IsFractionRing.injective (Polynomial K) (RatFunc K)).ne r.denom_ne_zero
    have hz := hr
    rw [← RatFunc.num_div_denom r, Derivation.leibniz_div] at hz
    simp only [smul_eq_mul, rationalParameterDerivative_polynomial] at hz
    have hW := (mul_eq_zero.mp hz).resolve_left (pow_ne_zero 2 (inv_ne_zero hdF))
    have hw : Polynomial.wronskian r.num r.denom = 0 := by
      apply IsFractionRing.injective (Polynomial K) (RatFunc K)
      simp only [Polynomial.wronskian, map_sub, map_mul, map_zero]
      linear_combination -hW
    obtain ⟨hn, hd⟩ := r.isCoprime_num_denom.wronskian_eq_zero_iff.mp hw
    refine ⟨r.num.coeff 0 / r.denom.coeff 0, ?_⟩
    calc
      r = algebraMap (Polynomial K) (RatFunc K) r.num /
          algebraMap (Polynomial K) (RatFunc K) r.denom := (RatFunc.num_div_denom r).symm
      _ = algebraMap (Polynomial K) (RatFunc K) (Polynomial.C (r.num.coeff 0)) /
          algebraMap (Polynomial K) (RatFunc K) (Polynomial.C (r.denom.coeff 0)) := by
        rw [← Polynomial.eq_C_of_derivative_eq_zero hn, ← Polynomial.eq_C_of_derivative_eq_zero hd]
      _ = _ := by
        change algebraMap K (RatFunc K) (r.num.coeff 0) /
          algebraMap K (RatFunc K) (r.denom.coeff 0) = _
        rw [map_div₀]
  · rintro ⟨c, rfl⟩
    exact (rationalParameterDerivative K).map_algebraMap c

/-- The whole actual constant intermediate field of the rational
parameter derivative is precisely the original coefficient field. -/
theorem rationalParameterDerivative_constant_field :
    derivationConstants (rationalParameterDerivative K) = ⊥ := by
  ext r
  change rationalParameterDerivative K r = 0 ↔ r ∈ (⊥ : IntermediateField K (RatFunc K))
  rw [rationalParameterDerivative_eq_zero_iff_scalar, IntermediateField.mem_bot]
  constructor
  · rintro ⟨c, hc⟩
    exact ⟨c, hc.symm⟩
  · rintro ⟨c, hc⟩
    exact ⟨c, hc.symm⟩

end DimensionFourDependence
