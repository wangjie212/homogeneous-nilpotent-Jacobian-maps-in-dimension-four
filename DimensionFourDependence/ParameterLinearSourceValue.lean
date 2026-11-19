import DimensionFourDependence.PrimitiveParameterLinearForm
import DimensionFourDependence.PolynomialScalarFactorRegularity

/-! # Source values of polynomial-parameter linear forms

The evaluated form lies in the source ring with the parameter adjoined.
Its source Euler weight is one whenever the parameter has weight zero.
A nonconstant polynomial scalar product therefore constructs an original
regular source polynomial representing the entire linear-form value.
-/

namespace DimensionFourDependence

open MvPolynomial

variable {K R F : Type*} [Field K] [CommRing R] [Field F]
    [Algebra K R] [Algebra K F] [Algebra R F] [IsScalarTower K R F] {m : ℕ}

omit [CommRing R] [Algebra K R] [Algebra R F] [IsScalarTower K R F] in
/-- The polynomial-parameter linear form has the explicit original
coordinate value given by its full coefficient pairing. -/
theorem polynomial_parameter_linear_form_source_value
    (t : F) (v : Fin m → Polynomial K) (x : Fin m → F) :
    MvPolynomial.eval₂ (Polynomial.aeval t).toRingHom x (polynomialParameterLinearForm v) =
      ∑ i, Polynomial.aeval t (v i) * x i := by
  simp only [polynomialParameterLinearForm, MvPolynomial.eval₂_sum,
    MvPolynomial.eval₂_mul, MvPolynomial.eval₂_C, MvPolynomial.eval₂_X]
  rfl

/-- Its entire source value lies in R[t], with the original source
coordinates included by their actual algebra map. -/
theorem polynomial_parameter_linear_form_source_value_mem_adjoin
    (t : F) (v : Fin m → Polynomial K) (x : Fin m → R) :
    MvPolynomial.eval₂ (Polynomial.aeval t).toRingHom
      (fun i => algebraMap R F (x i)) (polynomialParameterLinearForm v) ∈ Algebra.adjoin R {t} := by
  let J := Algebra.adjoin R ({t} : Set F)
  have hc (p : Polynomial K) : Polynomial.aeval t p ∈ J := by
    have hp := Polynomial.aeval_mem_adjoin_singleton R t (p := p.map (algebraMap K R))
    simpa only [Polynomial.aeval_map_algebraMap] using hp
  rw [polynomial_parameter_linear_form_source_value]
  exact J.sum_mem (fun i _ => J.mul_mem (hc (v i)) (J.algebraMap_mem (x i)))

omit [CommRing R] [Algebra K R] [Algebra R F] [IsScalarTower K R F] in
/-- A derivation with parameter weight zero and coordinate weights
one gives the evaluated polynomial-parameter linear form weight one. -/
theorem polynomial_parameter_linear_form_derivation_weight_one
    (D : Derivation K F F) (t : F) (ht : D t = 0)
    (v : Fin m → Polynomial K) (x : Fin m → F) (hx : ∀ i, D (x i) = x i) :
    D (MvPolynomial.eval₂ (Polynomial.aeval t).toRingHom x (polynomialParameterLinearForm v)) =
      MvPolynomial.eval₂ (Polynomial.aeval t).toRingHom x (polynomialParameterLinearForm v) := by
  have hc (p : Polynomial K) : D (Polynomial.aeval t p) = 0 := by
    rw [D.map_aeval, ht, smul_zero]
  simp only [polynomial_parameter_linear_form_source_value, map_sum, D.leibniz, hc, hx,
    smul_eq_mul, mul_zero, add_zero]

/-- The nonconstant polynomial scalar product constructs an actual
normal source-ring element with precisely the evaluated linear-form value. -/
theorem polynomial_parameter_linear_form_source_value_regular
    [IsDomain R] [IsIntegrallyClosed R] [IsFractionRing R F]
    (t : F) (v : Fin m → Polynomial K) (x : Fin m → R)
    (A : Polynomial K) (hA : 0 < A.natDegree) (d : ℕ) (H : R)
    (hH : algebraMap R F H = Polynomial.aeval t A *
      (MvPolynomial.eval₂ (Polynomial.aeval t).toRingHom
        (fun i => algebraMap R F (x i)) (polynomialParameterLinearForm v)) ^ d) :
    ∃ Z : R, algebraMap R F Z = MvPolynomial.eval₂ (Polynomial.aeval t).toRingHom
      (fun i => algebraMap R F (x i)) (polynomialParameterLinearForm v) :=
  source_factor_regular_of_nonconstant_polynomial_scalar t _
    (polynomial_parameter_linear_form_source_value_mem_adjoin t v x) A hA d H hH

end DimensionFourDependence
