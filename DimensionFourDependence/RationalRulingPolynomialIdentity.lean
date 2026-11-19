import DimensionFourDependence.BivariateAlgebraicPolynomialDescent
import DimensionFourDependence.IndependentGaussCoefficientRealization
import DimensionFourDependence.SegreRulingBinaryPolynomial
import Mathlib.Algebra.Polynomial.Bivariate

/-! # An actual factored ruling value constructs an exact rational polynomial restriction -/

namespace DimensionFourDependence

universe u
set_option maxHeartbeats 2500000

variable {K E : Type u} [Field K] [CharZero K] [Field E] [Algebra K E]

/-- The specified rational parameter embedding retains every original
polynomial value, not only its generator. -/
theorem transcendentalParameterFieldHom_polynomial (t : E) (ht : Transcendental K t)
    (p : Polynomial K) :
    transcendentalParameterFieldHom t ht (algebraMap (Polynomial K) (RatFunc K) p) =
      Polynomial.aeval t p := by
  simp only [transcendentalParameterFieldHom, IsLocalization.liftAlgHom_apply, IsLocalization.lift_eq]
  rfl

/-- The exact restriction of an original bivariate polynomial maps
through the original rational parameter embedding to coefficient evaluation. -/
theorem bivariate_rational_restriction_maps_to_parameter_evaluation
    (t : E) (ht : Transcendental K t) (P : Polynomial (Polynomial K)) :
    (P.map (algebraMap (Polynomial K) (RatFunc K))).map
        (transcendentalParameterFieldHom t ht).toRingHom =
      P.map (Polynomial.aeval t).toRingHom := by
  ext i
  simp only [Polynomial.coeff_map]
  exact transcendentalParameterFieldHom_polynomial t ht (P.coeff i)

/-- Derivative-constant affine covectors give a polynomial whose
every actual coefficient is a constant of the same derivation. -/
theorem ruling_power_polynomial_constant_coefficients
    (D : Derivation K E E) (a b : Fin 2 → E) (ha : ∀ i, D (a i) = 0)
    (hb : ∀ i, D (b i) = 0) (d : ℕ) :
    ∀ i, D ((segreRulingPowerPolynomial a b d).coeff i) = 0 := by
  let J := derivationConstants D
  let A : Fin 2 → J := fun i => ⟨a i, ha i⟩
  let B : Fin 2 → J := fun i => ⟨b i, hb i⟩
  have hm : (segreRulingPowerPolynomial A B d).map (algebraMap J E) =
      segreRulingPowerPolynomial a b d := by
    simp only [segreRulingPowerPolynomial, segreRulingAffineFactor,
      Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_add, Polynomial.map_C, Polynomial.map_X]
    rfl
  intro i
  rw [← hm, Polynomial.coeff_map]
  exact ((segreRulingPowerPolynomial A B d).coeff i).property

/-- A factored value with actual parameter-algebraic coefficients is
an exact polynomial restriction of the original bivariate polynomial.
Coordinate differentiation proves coefficient comparison internally. -/
theorem parameter_algebraic_factored_value_constructs_rational_ruling_identity
    (D : Derivation K E E) (s t : E) (hs : D s = 1) (ht0 : D t = 0)
    (ht : Transcendental K t) (P : Polynomial (Polynomial K))
    (a b : Fin 2 → E) (d : ℕ)
    (ha : ∀ i, IsAlgebraic (IntermediateField.adjoin K ({t} : Set E)) (a i))
    (hb : ∀ i, IsAlgebraic (IntermediateField.adjoin K ({t} : Set E)) (b i))
    (hvalue : Polynomial.eval₂ (Polynomial.aeval t).toRingHom s P =
      (segreRulingPowerPolynomial a b d).eval s) :
    (P.map (algebraMap (Polynomial K) (RatFunc K))).map
        (transcendentalParameterFieldHom t ht).toRingHom = segreRulingPowerPolynomial a b d := by
  rw [bivariate_rational_restriction_maps_to_parameter_evaluation]
  have hleft (i : ℕ) : D ((P.map (Polynomial.aeval t).toRingHom).coeff i) = 0 := by
    rw [Polynomial.coeff_map]
    change D (Polynomial.aeval t (P.coeff i)) = 0
    rw [D.map_aeval, ht0]
    simp
  have hright := ruling_power_polynomial_constant_coefficients D a b
    (fun i => derivation_zero_of_algebraic_parameter_constant D t ht0 _ (ha i))
    (fun i => derivation_zero_of_algebraic_parameter_constant D t ht0 _ (hb i)) d
  apply sub_eq_zero.mp
  apply polynomial_constant_coefficients_eval_zero_implies_zero D s hs
  · intro i
    rw [Polynomial.coeff_sub, map_sub, hleft, hright, sub_self]
  · rw [Polynomial.eval_sub, Polynomial.eval_map]
    exact sub_eq_zero.mpr hvalue

/-- The nested original coefficient evaluation is the usual bivariate
evaluation, with its two original coordinate positions explicit. -/
theorem bivariate_eval₂_eq_aevalAeval (P : Polynomial (Polynomial K)) (s t : E) :
    Polynomial.eval₂ (Polynomial.aeval t).toRingHom s P = Polynomial.aevalAeval t s P := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ => simp only [Polynomial.eval₂_add, map_add, hP, hQ]
  | monomial n a =>
    rw [← Polynomial.C_mul_X_pow_eq_monomial]
    simp only [Polynomial.eval₂_mul, Polynomial.eval₂_pow, Polynomial.eval₂_C, Polynomial.eval₂_X,
      map_mul, map_pow, Polynomial.aevalAeval_C, Polynomial.aevalAeval_Y]
    rfl

/-- Exchanging the two original variables exchanges their exact nested
evaluation values, so the second ruling uses the same original polynomial. -/
theorem bivariate_nested_evaluation_swap (P : Polynomial (Polynomial K)) (s t : E) :
    Polynomial.eval₂ (Polynomial.aeval t).toRingHom s (Polynomial.Bivariate.swap P) =
      Polynomial.eval₂ (Polynomial.aeval s).toRingHom t P := by
  rw [bivariate_eval₂_eq_aevalAeval, bivariate_eval₂_eq_aevalAeval,
    Polynomial.Bivariate.aevalAeval_swap]

end DimensionFourDependence
