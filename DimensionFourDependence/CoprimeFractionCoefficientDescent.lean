import DimensionFourDependence.Defs
import Mathlib.RingTheory.Localization.NumDen

/-! # Coprime multipliers force an actual fraction-field coefficient into the base ring -/

namespace DimensionFourDependence

set_option maxHeartbeats 1100000

section FractionDescent

variable {R F : Type*} [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R]
  [Field F] [Algebra R F] [IsFractionRing R F]

/-- A reduced denominator divides both coprime multipliers, so it is a
unit. This requires no Bézout relation in the polynomial coefficient ring. -/
theorem fraction_coefficient_descends_of_coprime_multiples
    (a b : R) (hc : IsRelPrime a b) (x : F)
    (ha : ∃ p : R, algebraMap R F p = algebraMap R F a * x)
    (hb : ∃ q : R, algebraMap R F q = algebraMap R F b * x) :
    ∃ z : R, algebraMap R F z = x := by
  obtain ⟨n,d,hnd,hx⟩ := IsFractionRing.exists_reduced_fraction R x
  let φ := algebraMap R F
  have hd : φ d ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors d.property
  have hx' : φ n = x * φ d := by
    rw [IsFractionRing.mk'_eq_div] at hx
    exact (div_eq_iff hd).mp hx
  have hdiv (r : R) (hr : ∃ p : R, φ p = φ r * x) : (d : R) ∣ r := by
    obtain ⟨p,hp⟩ := hr
    have he : r * n = (d : R) * p := by
      apply IsFractionRing.injective R F
      change φ (r * n) = φ ((d : R) * p)
      simp only [map_mul, hx', hp]
      ring
    exact hnd.symm.dvd_of_dvd_mul_right ⟨p,he⟩
  obtain ⟨u, hu⟩ := hc (hdiv a ha) (hdiv b hb)
  refine ⟨n * (↑u⁻¹ : R), ?_⟩
  apply mul_right_cancel₀ hd
  rw [map_mul, mul_assoc]
  have he : φ (↑u⁻¹ : R) * φ d = 1 := by
    rw [← map_mul, ← hu]
    simp
  rw [he, mul_one, hx']

end FractionDescent

/-- A scalar change of the variable multiplies each univariate
coefficient by the corresponding power of the scalar. -/
theorem polynomial_coeff_comp_C_mul_X {R : Type*} [CommRing R]
    (p : Polynomial R) (a : R) (j : ℕ) :
    (p.comp (Polynomial.C a * Polynomial.X)).coeff j = a ^ j * p.coeff j := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    simp only [Polynomial.add_comp, Polynomial.coeff_add, hp, hq, mul_add]
  | monomial n c =>
    rw [Polynomial.monomial_comp, mul_pow, ← Polynomial.C_pow, ← mul_assoc,
      ← map_mul, Polynomial.C_mul_X_pow_eq_monomial, Polynomial.coeff_monomial,
      Polynomial.coeff_monomial]
    by_cases h : n = j
    · subst n
      simp [mul_comm]
    · simp [h, Ne.symm h]

end DimensionFourDependence
