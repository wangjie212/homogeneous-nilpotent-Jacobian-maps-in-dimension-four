import DimensionFourDependence.ActualPrimitiveConeForms
import DimensionFourDependence.SourceEulerLinearFactor

/-! # Independent transverse coordinates identify the fixed Gauss covector

After the evaluated source factor is a fixed ternary linear form,
independence over the actual closed Gauss field identifies every parameter
coefficient with the corresponding original constant. The original reduced
pencil supplies the independence; the changed cover may be any equivalence
of the same actual closed field.
-/

namespace DimensionFourDependence

open MvPolynomial

set_option quotPrecheck false
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 100000

/-- Independent coordinates identify all coefficients of linear forms
from equality of their complete source values. -/
theorem independent_linear_form_values_identify_coefficients
    {B F : Type*} [Field B] [Field F] [Algebra B F] {n : ℕ}
    (x : Fin n → F) (hx : AlgebraicIndependent B x)
    (a b : Fin n → B)
    (h : aeval x (linearFormPolynomial a) = aeval x (linearFormPolynomial b)) : a = b := by
  have hp := hx h
  funext i
  have hc := congrArg (pderiv i) hp
  rw [linearFormPolynomial_pderiv, linearFormPolynomial_pderiv] at hc
  exact MvPolynomial.C_injective (Fin n) B hc

variable {K : Type*} [Field K] [CharZero K]
    (H : Fin 4 → MvPolynomial (Fin 4) K) (I : ImageRelationWitness H)

local notation "S₀" => FractionRing (MvPolynomial (Fin 4) K)
local notation "C₀" => closedGaussParameterField H I
local notation "x₀" => (fun i : Fin 3 => rationalCoordinate (K := K) i.castSucc)

/-- A polynomial-parameter covector whose evaluated source value is
an actual fixed ternary linear form has constant polynomial coefficients.
The original reduced pencil constructs the required independence over
the entire closed Gauss field, even after changing its parameter. -/
theorem actual_gauss_polynomial_covector_constant_of_fixed_ternary_source_value
    (e₀ e : RatFunc K ≃ₐ[K] C₀)
    (p q : MvPolynomial (Fin 4) K) (hp0 : p ≠ 0) (hq0 : q ≠ 0) (hrel : IsRelPrime p q)
    {a b : ℕ} (hp : p.IsHomogeneous a) (hq : q.IsHomogeneous b)
    (hparameter : closedGaussParameterSourceHom H I e₀ RatFunc.X =
      algebraMap (MvPolynomial (Fin 4) K) S₀ p / algebraMap (MvPolynomial (Fin 4) K) S₀ q)
    (hvertex : 0 < p.degreeOf (Fin.last 3) ∨ 0 < q.degreeOf (Fin.last 3))
    (v : Fin 3 → Polynomial K) (c : Fin 3 → K)
    (hvalue : MvPolynomial.eval₂ (Polynomial.aeval
        (closedGaussParameterSourceHom H I e RatFunc.X)).toRingHom x₀ (polynomialParameterLinearForm v) =
      algebraMap (MvPolynomial (Fin 4) K) S₀ (rename Fin.castSucc (linearFormPolynomial c))) :
    ∀ i, v i = Polynomial.C (c i) := by
  let f := closedGaussParameterSourceHom H I e
  have hx := actual_closed_gauss_vertex_pencil_transverse_source_independent
    H I e₀ p q hp0 hq0 hrel hp hq hparameter hvertex
  have heval (i : Fin 3) : algebraMap C₀ S₀ (e (algebraMap (Polynomial K) (RatFunc K) (v i))) =
      Polynomial.aeval (f RatFunc.X) (v i) := rational_function_algHom_polynomial_value f (v i)
  have hsource : algebraMap (MvPolynomial (Fin 4) K) S₀ (rename Fin.castSucc (linearFormPolynomial c)) =
      ∑ i : Fin 3, algebraMap K S₀ (c i) * rationalCoordinate (K := K) i.castSucc := by
    simp only [linearFormPolynomial, map_sum, map_mul, rename_C, rename_X]
    simp only [← MvPolynomial.algebraMap_eq,
      ← IsScalarTower.algebraMap_apply K (MvPolynomial (Fin 4) K) S₀, rationalCoordinate]
  have hpair : aeval x₀ (linearFormPolynomial (fun i => e (algebraMap (Polynomial K) (RatFunc K) (v i)))) =
      aeval x₀ (linearFormPolynomial (fun i => algebraMap K C₀ (c i))) := by
    simp only [linearFormPolynomial, map_sum, map_mul, aeval_C, aeval_X, heval,
      ← IsScalarTower.algebraMap_apply K C₀ S₀]
    rw [← polynomial_parameter_linear_form_source_value, hvalue, hsource]
  have hcoeff := independent_linear_form_values_identify_coefficients x₀ hx _ _ hpair
  intro i
  apply RatFunc.algebraMap_injective K
  apply e.injective
  change e (algebraMap (Polynomial K) (RatFunc K) (v i)) = e (algebraMap K (RatFunc K) (c i))
  rw [AlgEquiv.commutes]
  exact congrFun hcoeff i

end DimensionFourDependence
