import DimensionFourDependence.LinearPowerQuotientRecovery
import DimensionFourDependence.PrimitiveParameterLinearForm

/-! # A fixed linear factor has a polynomial-parameter linear quotient

A nonzero original constant covector has a unit pivot in K[t]. The
coordinate-point quotient recovery therefore returns its complete linear
quotient over K[t] from a factorization over K(t). Proportional rational
linear factors are absorbed into that quotient without changing the form.
-/

namespace DimensionFourDependence

open MvPolynomial

variable {K : Type*} [Field K] {n : ℕ}

/-- A fourth-coordinate form polynomial in the parameter has a
polynomial linear quotient by a power of a fixed original linear form. -/
theorem fixed_linear_power_rational_quotient_has_polynomial_coefficients
    (c : Fin n → K) (hc : c ≠ 0) (P : MvPolynomial (Fin n) (Polynomial K))
    (r : ℕ) (b : Fin n → RatFunc K)
    (hP : MvPolynomial.map (algebraMap (Polynomial K) (RatFunc K)) P =
      linearFormPolynomial (fun i => algebraMap K (RatFunc K) (c i)) ^ r * linearFormPolynomial b) :
    ∃ m : Fin n → Polynomial K,
      (∀ i, algebraMap (Polynomial K) (RatFunc K) (m i) = b i) ∧
      P = polynomialParameterLinearForm (fun i => Polynomial.C (c i)) ^ r * polynomialParameterLinearForm m := by
  classical
  obtain ⟨j, hj⟩ : ∃ j, c j ≠ 0 := by
    simpa only [ne_eq, funext_iff, Pi.zero_apply, not_forall] using hc
  have hunit : IsUnit (Polynomial.C (c j)) := (isUnit_iff_ne_zero.mpr hj).map Polynomial.C
  have hP' : MvPolynomial.map (algebraMap (Polynomial K) (RatFunc K)) P =
      coefficientLinearForm (fun i => algebraMap (Polynomial K) (RatFunc K) (Polynomial.C (c i))) ^ r *
        coefficientLinearForm b := hP
  obtain ⟨m, hm, hwhole⟩ := unit_pivot_linear_power_quotient_descends
    (algebraMap (Polynomial K) (RatFunc K)) (RatFunc.algebraMap_injective K)
    P (fun i => Polynomial.C (c i)) j hunit r b hP'
  exact ⟨m, hm, hwhole⟩

/-- A proportional rational common factor is absorbed into the fourth
linear quotient, whose entire coefficients are then recovered in K[t]. -/
theorem proportional_linear_power_quotient_constructs_polynomial_coefficients
    (c : Fin n → K) (hc : c ≠ 0) (P : MvPolynomial (Fin n) (Polynomial K))
    (r : ℕ) (a b : Fin n → RatFunc K) (s : RatFunc K)
    (ha : ∀ i, a i = s * algebraMap K (RatFunc K) (c i))
    (hP : MvPolynomial.map (algebraMap (Polynomial K) (RatFunc K)) P =
      linearFormPolynomial a ^ r * linearFormPolynomial b) :
    ∃ m : Fin n → Polynomial K,
      (∀ i, algebraMap (Polynomial K) (RatFunc K) (m i) = s ^ r * b i) ∧
      P = polynomialParameterLinearForm (fun i => Polynomial.C (c i)) ^ r * polynomialParameterLinearForm m := by
  have hlin : linearFormPolynomial a = C s *
      linearFormPolynomial (fun i => algebraMap K (RatFunc K) (c i)) := by
    simp only [linearFormPolynomial, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [ha i, map_mul, mul_assoc]
  apply fixed_linear_power_rational_quotient_has_polynomial_coefficients c hc P r
    (fun i => s ^ r * b i)
  rw [hP, hlin, mul_pow]
  have hscale : linearFormPolynomial (fun i => s ^ r * b i) = C (s ^ r) * linearFormPolynomial b :=
    coefficientLinearForm_mul_coefficients _ _
  rw [hscale, ← map_pow]
  ring

end DimensionFourDependence
