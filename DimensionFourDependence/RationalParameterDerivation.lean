import DimensionFourDependence.RationalPartial
import DimensionFourDependence.PrimitiveRationalVector

/-! # Differentiation in the actual rational Gauss parameter

Transport the checked one-coordinate rational partial derivative through
the actual one-variable fraction-field equivalence. This gives a bundled
derivation of the actual rational-function field, with parameter derivative
one, the actual polynomial derivative, and the chain rule under every
coefficient-field algebra homomorphism and derivation.
-/

namespace DimensionFourDependence

section Conjugation

variable {K F G : Type*} [Field K] [Field F] [Field G] [Algebra K F] [Algebra K G]

/-- Transport an actual field derivation through an algebra equivalence. -/
noncomputable def fieldDerivationConjugate (e : F ≃ₐ[K] G) (D : Derivation K F F) :
    Derivation K G G where
  toLinearMap := e.toLinearMap.comp (D.toLinearMap.comp e.symm.toLinearMap)
  map_one_eq_zero' := by
    change e (D (e.symm 1)) = 0
    rw [map_one, D.map_one_eq_zero, map_zero]
  leibniz' := by
    intro a b
    change e (D (e.symm (a * b))) = a * e (D (e.symm b)) + b * e (D (e.symm a))
    rw [map_mul, D.leibniz]
    simp only [smul_eq_mul, map_add, map_mul, e.apply_symm_apply]

/-- The transported derivation has the required value on every image. -/
theorem fieldDerivationConjugate_apply (e : F ≃ₐ[K] G) (D : Derivation K F F) (x : F) :
    fieldDerivationConjugate e D (e x) = e (D x) := by
  change e (D (e.symm (e x))) = e (D x)
  rw [e.symm_apply_apply]

end Conjugation

variable (K : Type*) [Field K]

/-- The actual one-coordinate multivariate source field is the actual
one-variable rational-function field over the same original coefficients. -/
noncomputable def oneVariableRationalEquiv :
    FractionRing (MvPolynomial (Fin 1) K) ≃ₐ[K] RatFunc K :=
  IsFractionRing.algEquivOfAlgEquiv
    (K := FractionRing (MvPolynomial (Fin 1) K)) (L := RatFunc K)
    (MvPolynomial.uniqueAlgEquiv K (Fin 1))

/-- The actual single source coordinate is carried to the rational parameter. -/
theorem oneVariableRationalEquiv_coordinate :
    oneVariableRationalEquiv K (rationalCoordinate (K := K) (n := 1) 0) = RatFunc.X := by
  change (IsFractionRing.algEquivOfAlgEquiv
    (K := FractionRing (MvPolynomial (Fin 1) K)) (L := RatFunc K)
    (MvPolynomial.uniqueAlgEquiv K (Fin 1)))
      (algebraMap (MvPolynomial (Fin 1) K) _ (MvPolynomial.X 0)) = _
  rw [IsFractionRing.algEquivOfAlgEquiv_algebraMap]
  have hX : MvPolynomial.uniqueAlgEquiv K (Fin 1) (MvPolynomial.X 0) = Polynomial.X := by
    change MvPolynomial.eval₂ Polynomial.C (fun _ => Polynomial.X) (MvPolynomial.X 0) = Polynomial.X
    rw [MvPolynomial.eval₂_X]
  rw [hX, RatFunc.algebraMap_X]

/-- The actual derivative with respect to the rational parameter. -/
noncomputable def rationalParameterDerivative : Derivation K (RatFunc K) (RatFunc K) :=
  fieldDerivationConjugate (oneVariableRationalEquiv K) (rationalPartial (K := K) (n := 1) 0)

/-- The actual rational parameter has derivative one. -/
theorem rationalParameterDerivative_X : rationalParameterDerivative K RatFunc.X = 1 := by
  rw [← oneVariableRationalEquiv_coordinate K]
  change fieldDerivationConjugate (oneVariableRationalEquiv K) (rationalPartial (K := K) (n := 1) 0)
    (oneVariableRationalEquiv K (rationalCoordinate (K := K) (n := 1) 0)) = 1
  rw [fieldDerivationConjugate_apply, rationalPartial_coordinate]
  simp

/-- The rational parameter derivation restricts to the actual
polynomial derivative on every original polynomial. -/
theorem rationalParameterDerivative_polynomial (p : Polynomial K) :
    rationalParameterDerivative K (algebraMap (Polynomial K) (RatFunc K) p) =
      algebraMap (Polynomial K) (RatFunc K) p.derivative := by
  have he : (rationalParameterDerivative K).compAlgebraMap (Polynomial K) =
      Polynomial.mkDerivation K (1 : RatFunc K) := by
    apply Polynomial.derivation_ext
    change rationalParameterDerivative K (algebraMap (Polynomial K) (RatFunc K) Polynomial.X) = _
    rw [RatFunc.algebraMap_X, rationalParameterDerivative_X, Polynomial.mkDerivation_X]
  have hh := DFunLike.congr_fun he p
  simpa only [Derivation.compAlgebraMap_apply, Polynomial.mkDerivation_apply, Algebra.smul_def, mul_one] using hh

variable {K} {F : Type*} [Field F] [Algebra K F]

/-- The polynomial chain rule for an actual image of the rational parameter. -/
theorem rational_parameter_polynomial_chain_rule
    (f : RatFunc K →ₐ[K] F) (D : Derivation K F F) (p : Polynomial K) :
    D (f (algebraMap (Polynomial K) (RatFunc K) p)) =
      f (algebraMap (Polynomial K) (RatFunc K) p.derivative) * D (f RatFunc.X) := by
  rw [rational_function_algHom_polynomial_value, rational_function_algHom_polynomial_value]
  simpa only [smul_eq_mul] using D.map_aeval p (f RatFunc.X)

/-- The full rational chain rule for every actual rational function,
algebra homomorphism, and ambient coefficient derivation. -/
theorem rational_parameter_chain_rule
    (f : RatFunc K →ₐ[K] F) (D : Derivation K F F) (r : RatFunc K) :
    D (f r) = f (rationalParameterDerivative K r) * D (f RatFunc.X) := by
  obtain ⟨p, q, _, rfl⟩ := IsFractionRing.div_surjective (A := Polynomial K) r
  rw [map_div₀, D.leibniz_div, Derivation.leibniz_div]
  simp only [smul_eq_mul, map_mul, map_sub, map_pow, map_inv₀,
    rationalParameterDerivative_polynomial, rational_parameter_polynomial_chain_rule]
  ring

end DimensionFourDependence
