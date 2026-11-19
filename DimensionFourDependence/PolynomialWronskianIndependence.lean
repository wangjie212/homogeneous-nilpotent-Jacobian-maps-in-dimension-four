import DimensionFourDependence.RationalParameterConstants

/-! # Independent original parameter polynomials have nonzero Wronskian -/

namespace DimensionFourDependence

open Polynomial

set_option maxHeartbeats 2000000

variable {K : Type*} [Field K] [CharZero K]

/-- A zero Wronskian makes the exact ratio of the two original
polynomials a constant rational function, so its numerator is an
original scalar multiple of its nonzero denominator. -/
theorem polynomial_zero_wronskian_constructs_constant_multiple
    (f g : Polynomial K) (hg : g ≠ 0) (hW : Polynomial.wronskian f g = 0) :
    ∃ c : K, f = Polynomial.C c * g := by
  let φ := algebraMap (Polynomial K) (RatFunc K)
  have hgF : φ g ≠ 0 := fun hz => hg
    (IsFractionRing.injective (Polynomial K) (RatFunc K) (hz.trans (map_zero _).symm))
  have hWr : φ f * φ g.derivative - φ f.derivative * φ g = 0 := by
    simpa only [Polynomial.wronskian, map_sub, map_mul, map_zero] using congrArg φ hW
  have hD : rationalParameterDerivative K (φ f / φ g) = 0 := by
    rw [Derivation.leibniz_div]
    simp only [smul_eq_mul]
    rw [show rationalParameterDerivative K (φ f) = φ f.derivative from
      rationalParameterDerivative_polynomial K f,
      show rationalParameterDerivative K (φ g) = φ g.derivative from
      rationalParameterDerivative_polynomial K g]
    have he : φ g * φ f.derivative - φ f * φ g.derivative = 0 := by
      linear_combination -hWr
    rw [he, mul_zero]
  obtain ⟨c, hc⟩ := (rationalParameterDerivative_eq_zero_iff_scalar (φ f / φ g)).mp hD
  refine ⟨c, ?_⟩
  apply IsFractionRing.injective (Polynomial K) (RatFunc K)
  change φ f = φ (Polynomial.C c * g)
  rw [map_mul]
  change φ f = algebraMap K (RatFunc K) c * φ g
  exact (div_eq_iff hgF).mp hc

/-- Linear independence of two actual original parameter polynomials
excludes a zero Wronskian without a coprimality assumption. -/
theorem independent_parameter_polynomials_wronskian_ne_zero
    (f g : Polynomial K) (hfg : LinearIndependent K ![f, g]) :
    Polynomial.wronskian f g ≠ 0 := by
  intro hW
  have hg : g ≠ 0 := by simpa using hfg.ne_zero (1 : Fin 2)
  obtain ⟨c, hc⟩ := polynomial_zero_wronskian_constructs_constant_multiple f g hg hW
  have hrel : (1 : K) • f + (-c) • g = 0 := by
    rw [hc, one_smul, Polynomial.smul_eq_C_mul]
    simp
  have hone : (1 : K) = 0 := ((LinearIndependent.pair_iff.mp hfg) 1 (-c) hrel).1
  exact one_ne_zero hone

end DimensionFourDependence
