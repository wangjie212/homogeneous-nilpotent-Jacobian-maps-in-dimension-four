import DimensionFourDependence.PolynomialWronskianIndependence

/-! # The exact moving-output minor is a parameter Wronskian -/

namespace DimensionFourDependence

set_option maxHeartbeats 2000000

variable {K F : Type*} [Field K] [CharZero K] [Field F] [Algebra K F]

/-- All derivatives of the common scalar cancel from the two-output
minor. The surviving factor is the actual parameter derivative times
the original polynomial Wronskian. -/
theorem scaled_parameter_derivation_minor_identity
    (D : Derivation K F F) (s t : F) (f g : Polynomial K) :
    (s * Polynomial.aeval t f) * D (s * Polynomial.aeval t g) -
      (s * Polynomial.aeval t g) * D (s * Polynomial.aeval t f) =
        s ^ 2 * D t * Polynomial.aeval t (Polynomial.wronskian f g) := by
  rw [D.leibniz, D.leibniz, D.map_aeval, D.map_aeval]
  simp only [smul_eq_mul, Polynomial.wronskian, map_sub, map_mul]
  ring

/-- A nonzero actual parameter derivative and two independent
parameter polynomials make their actual moving-output minor nonzero.
Parameter transcendence is derived from that derivative. -/
theorem independent_scaled_parameter_derivation_minor_ne_zero
    (D : Derivation K F F) (s t : F) (hs : s ≠ 0) (ht : D t ≠ 0)
    (f g : Polynomial K) (hfg : LinearIndependent K ![f, g]) :
    (s * Polynomial.aeval t f) * D (s * Polynomial.aeval t g) -
      (s * Polynomial.aeval t g) * D (s * Polynomial.aeval t f) ≠ 0 := by
  have htrans : Transcendental K t := fun ha => ht (derivation_zero_of_isAlgebraic D t ha)
  have hW : Polynomial.aeval t (Polynomial.wronskian f g) ≠ 0 := by
    intro hz
    exact independent_parameter_polynomials_wronskian_ne_zero f g hfg
      ((transcendental_iff_injective.mp htrans) (hz.trans (map_zero _).symm))
  rw [scaled_parameter_derivation_minor_identity]
  exact mul_ne_zero (mul_ne_zero (pow_ne_zero 2 hs) ht) hW

end DimensionFourDependence
