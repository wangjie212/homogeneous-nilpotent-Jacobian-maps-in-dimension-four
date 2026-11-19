import DimensionFourDependence.FiberPolynomialGradients
import DimensionFourDependence.PrimitiveRationalVector

/-! # Primitive polynomial-parameter covectors have no finite base point -/

namespace DimensionFourDependence

open MvPolynomial

variable {K : Type*} [Field K] {n : ℕ}

/-- The ternary linear form with coefficients in the polynomial parameter ring. -/
noncomputable def polynomialParameterLinearForm (v : Fin n → Polynomial K) :
    MvPolynomial (Fin n) (Polynomial K) := ∑ i, C (v i) * X i

/-- Polynomial parameter coefficient inclusion gives the same rational linear form. -/
theorem polynomialParameterLinearForm_map (v : Fin n → Polynomial K) :
    MvPolynomial.map (algebraMap (Polynomial K) (RatFunc K)) (polynomialParameterLinearForm v) =
      linearFormPolynomial (fun i => algebraMap (Polynomial K) (RatFunc K) (v i)) := by
  simp only [polynomialParameterLinearForm, linearFormPolynomial, map_sum, map_mul,
    MvPolynomial.map_C, MvPolynomial.map_X]

/-- Constant parameter specialization retains the complete linear form. -/
theorem polynomialParameterLinearForm_specialize (v : Fin n → Polynomial K) (a : K) :
    MvPolynomial.map (Polynomial.evalRingHom a) (polynomialParameterLinearForm v) =
      linearFormPolynomial (fun i => (v i).eval a) := by
  simp only [polynomialParameterLinearForm, linearFormPolynomial, map_sum, map_mul,
    MvPolynomial.map_C, MvPolynomial.map_X]
  rfl

/-- Primitive polynomial coefficients cannot all vanish at a constant
parameter value, because X-a would then divide every coefficient. -/
theorem primitive_parameter_covector_no_constant_base_point
    (v : Fin n → Polynomial K)
    (hprimitive : ∀ r : Polynomial K, (∀ i, r ∣ v i) → IsUnit r) (a : K) :
    ∃ i : Fin n, (v i).eval a ≠ 0 := by
  classical
  by_contra! hzero
  exact Polynomial.not_isUnit_X_sub_C a (hprimitive _ fun i => Polynomial.dvd_iff_isRoot.mpr (hzero i))

/-- Every finite specialization of every power of the primitive
polynomial linear form is nonzero. -/
theorem primitive_parameter_linear_power_specialization_ne_zero
    (v : Fin n → Polynomial K)
    (hprimitive : ∀ r : Polynomial K, (∀ i, r ∣ v i) → IsUnit r) (d : ℕ) (a : K) :
    MvPolynomial.map (Polynomial.evalRingHom a) (polynomialParameterLinearForm v ^ d) ≠ 0 := by
  obtain ⟨i, hi⟩ := primitive_parameter_covector_no_constant_base_point v hprimitive a
  rw [map_pow, polynomialParameterLinearForm_specialize]
  apply pow_ne_zero
  intro hz
  have hc := congrArg (pderiv i) hz
  rw [linearFormPolynomial_pderiv, map_zero] at hc
  exact MvPolynomial.C_ne_zero.mpr hi hc

end DimensionFourDependence
