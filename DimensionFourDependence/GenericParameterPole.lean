import DimensionFourDependence.PrimitiveParameterDenominator
import DimensionFourDependence.PolynomialPolePullback
import DimensionFourDependence.PrimitiveRationalVector
import Mathlib.RingTheory.AlgebraicIndependent.Basic

/-! # Constant coefficient poles survive at generic source coordinates

Moving the independent ternary coordinates into the coefficient field
turns a parameter numerator form into a univariate polynomial. At a
constant parameter value its specialization is the original numerator
form evaluated at these coordinates. Algebraic independence prevents
cancellation. A polynomial original-source value therefore constructs
a polynomial reciprocal parameter at each genuine constant pole.
-/

namespace DimensionFourDependence

variable {K L F σ : Type*} [Field K] [Field L] [Algebra K L]

/-- Regard the source coordinates as coefficients and retain the
Gauss parameter as the sole polynomial variable. -/
noncomputable def parameterNumeratorPolynomial (x : σ → L)
    (N : MvPolynomial σ (Polynomial K)) : Polynomial L :=
  MvPolynomial.eval₂ (Polynomial.mapRingHom (algebraMap K L))
    (fun i => Polynomial.C (x i)) N

/-- Constant parameter specialization commutes with evaluation at the
actual transverse source coordinates. -/
theorem parameterNumeratorPolynomial_eval (x : σ → L)
    (N : MvPolynomial σ (Polynomial K)) (a : K) :
    (parameterNumeratorPolynomial x N).eval (algebraMap K L a) =
      MvPolynomial.aeval x (MvPolynomial.map (Polynomial.evalRingHom a) N) := by
  induction N using MvPolynomial.induction_on with
  | C c =>
      simp only [parameterNumeratorPolynomial, MvPolynomial.eval₂_C, MvPolynomial.map_C, MvPolynomial.aeval_C]
      change (c.map (algebraMap K L)).eval (algebraMap K L a) = algebraMap K L (c.eval a)
      exact Polynomial.eval_map_apply _ _
  | add P Q hP hQ => simp only [parameterNumeratorPolynomial, MvPolynomial.eval₂_add,
      Polynomial.eval_add, map_add] at *; exact congrArg₂ (· + ·) hP hQ
  | mul_X P i hP =>
      change _ = _ at hP
      simpa only [parameterNumeratorPolynomial, MvPolynomial.eval₂_mul, MvPolynomial.eval₂_X,
        Polynomial.eval_mul, Polynomial.eval_C, map_mul, MvPolynomial.map_X, MvPolynomial.aeval_X] using
        congrArg (fun z : L => z * x i) hP

/-- A nonzero specialized numerator cannot vanish at algebraically
independent source coordinates. Thus its coefficient pole remains an
actual pole after the generic source coordinates become constants. -/
theorem parameterNumeratorPolynomial_nonzero_at_constant
    (x : σ → L) (hx : AlgebraicIndependent K x)
    (N : MvPolynomial σ (Polynomial K)) (a : K)
    (hN : MvPolynomial.map (Polynomial.evalRingHom a) N ≠ 0) :
    (parameterNumeratorPolynomial x N).eval (algebraMap K L a) ≠ 0 := by
  rw [parameterNumeratorPolynomial_eval]
  exact fun hz => hN (hx (by simpa using hz))

variable [Field F] [Algebra K F] [Algebra L F] [IsScalarTower K L F]

/-- Evaluating the parameter after moving transverse coordinates to
the coefficient field recovers the original mixed evaluation. -/
theorem parameterNumeratorPolynomial_aeval (x : σ → L)
    (N : MvPolynomial σ (Polynomial K)) (t : F) :
    Polynomial.aeval t (parameterNumeratorPolynomial x N) =
      MvPolynomial.eval₂ (Polynomial.aeval t).toRingHom
        (fun i => algebraMap L F (x i)) N := by
  induction N using MvPolynomial.induction_on with
  | C c => simp [parameterNumeratorPolynomial, Polynomial.aeval_map_algebraMap]
  | add P Q hP hQ => simp only [parameterNumeratorPolynomial, MvPolynomial.eval₂_add,
      map_add] at *; exact congrArg₂ (· + ·) hP hQ
  | mul_X P i hP =>
      simpa only [parameterNumeratorPolynomial, MvPolynomial.eval₂_mul, MvPolynomial.eval₂_X,
        map_mul, Polynomial.aeval_C] using
        congrArg (fun z : F => z * algebraMap L F (x i)) hP

/-- Clearing the actual rational-parameter coefficient denominator
preserves the original map value as a univariate polynomial relation
over the transverse-coordinate field. -/
theorem parameter_form_source_value_cleared_relation
    (x : σ → L) (f : RatFunc K →ₐ[K] F)
    (P : MvPolynomial σ (RatFunc K)) (D : Polynomial K)
    (N : MvPolynomial σ (Polynomial K))
    (hN : MvPolynomial.map (algebraMap (Polynomial K) (RatFunc K)) N =
      MvPolynomial.C (algebraMap (Polynomial K) (RatFunc K) D) * P)
    (H : F)
    (hH : MvPolynomial.eval₂ f.toRingHom (fun i => algebraMap L F (x i)) P = H) :
    Polynomial.aeval (f RatFunc.X) (parameterNumeratorPolynomial x N) =
      H * Polynomial.aeval (f RatFunc.X) (D.map (algebraMap K L)) := by
  have hc : f.toRingHom.comp (algebraMap (Polynomial K) (RatFunc K)) =
      (Polynomial.aeval (f RatFunc.X)).toRingHom := by
    apply RingHom.ext
    intro p
    exact rational_function_algHom_polynomial_value f p
  have heq := congrArg (MvPolynomial.eval₂Hom f.toRingHom
    (fun i => algebraMap L F (x i))) hN
  simp only [MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_map, MvPolynomial.eval₂_mul,
    MvPolynomial.eval₂_C, hc, hH] at heq
  rw [parameterNumeratorPolynomial_aeval, Polynomial.aeval_map_algebraMap]
  have hfD : f.toRingHom (algebraMap (Polynomial K) (RatFunc K) D) =
      Polynomial.aeval (f RatFunc.X) D := rational_function_algHom_polynomial_value f D
  rw [hfD] at heq
  exact heq.trans (mul_comm _ _)

variable [Algebra (Polynomial L) F] [IsScalarTower L (Polynomial L) F]
    [IsFractionRing (Polynomial L) F]

/-- A descended form with a polynomial original-source value supplies
its own reduced common denominator. Every constant denominator root
constructs a nonconstant polynomial reciprocal of the actual parameter;
no generic-pole persistence or pole-pullback assertion is supplied. -/
theorem generic_parameter_form_constructs_reduced_pole_pullback
    (x : σ → L) (hx : AlgebraicIndependent K x)
    (f : RatFunc K →ₐ[K] F)
    (ht : ¬ ∃ c : L, algebraMap L F c = f RatFunc.X)
    (P : MvPolynomial σ (RatFunc K)) (H : Polynomial L)
    (hH : MvPolynomial.eval₂ f.toRingHom (fun i => algebraMap L F (x i)) P =
      algebraMap (Polynomial L) F H) :
    ∃ D : Polynomial K, D ≠ 0 ∧ ∃ N : MvPolynomial σ (Polynomial K),
      MvPolynomial.map (algebraMap (Polynomial K) (RatFunc K)) N =
        MvPolynomial.C (algebraMap (Polynomial K) (RatFunc K) D) * P ∧
      ∀ a : K, D.eval a = 0 → ∃ U : Polynomial L, 0 < U.natDegree ∧
        algebraMap (Polynomial L) F U =
          (f RatFunc.X - algebraMap K F a)⁻¹ := by
  obtain ⟨D, hD, N, hN, hpole⟩ := parameter_form_reduced_common_denominator P
  refine ⟨D, hD, N, hN, ?_⟩
  intro a ha
  have hn := parameterNumeratorPolynomial_nonzero_at_constant x hx N a (hpole a ha)
  have hd : (D.map (algebraMap K L)).eval (algebraMap K L a) = 0 := by
    simp [ha]
  have hvalue := parameter_form_source_value_cleared_relation x f P D N hN _ hH
  obtain ⟨U, hdegree, hU⟩ := constant_pole_constructs_nonconstant_polynomial_parameter
    (f RatFunc.X) ht (parameterNumeratorPolynomial x N) (D.map (algebraMap K L))
    (algebraMap K L a) hd hn H hvalue
  refine ⟨U, hdegree, ?_⟩
  simpa only [← IsScalarTower.algebraMap_apply K L F] using hU

end DimensionFourDependence
