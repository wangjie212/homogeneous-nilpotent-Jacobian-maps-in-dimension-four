import DimensionFourDependence.IteratedDerivationPolynomial
import DimensionFourDependence.GaussParameterSurfaceDimension
import DimensionFourDependence.CoefficientEuler

/-! # Repeated integration of actual parameter-algebraic coefficients -/

namespace DimensionFourDependence

universe u
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 100000

variable {K E : Type u} [Field K] [CharZero K] [Field E] [Algebra K E]
attribute [local instance] coefficientFieldScalarTower

/-- The canonical partial on the actual algebraic parameter curve is
compatible with every ambient derivation taking value one at its parameter. -/
theorem parameter_coefficient_partial_compatible_with_ambient
    (Y : Fin 1 → E) (hY : AlgebraicIndependent K Y) (D : Derivation K E E)
    (hD : D (Y 0) = 1) :
    ∀ a : coefficientField (K := K) Y,
      D (algebraMap (coefficientField (K := K) Y) E a) =
        algebraMap (coefficientField (K := K) Y) E (coefficientPartial Y hY 0 a) := by
  let C := coefficientField (K := K) Y
  let δ := coefficientPartial Y hY 0
  let t : C := coefficientCoordinate (K := K) Y 0
  have ht : δ t = 1 := by
    simpa only [δ, t, coefficientCoordinate, ite_true] using coefficientPartial_coordinate Y hY 0 0
  have htrans : Transcendental K t := by
    intro ha
    have hz := derivation_zero_of_isAlgebraic δ t ha
    exact one_ne_zero (ht.symm.trans hz)
  have htr : Algebra.trdeg K C ≤ 1 := (independent_output_coefficientField_absolute_trdeg Y hY).le
  apply curve_derivation_compatible_of_parameter δ D t htrans htr
  change D (Y 0) = algebraMap C E (δ t)
  rw [hD, ht, map_one]

/-- All iterated actual ambient derivatives retain the uniquely
constructed derivative on the original algebraic parameter curve. -/
theorem parameter_coefficient_partial_iterate_compatible
    (Y : Fin 1 → E) (hY : AlgebraicIndependent K Y) (D : Derivation K E E)
    (hD : D (Y 0) = 1) (n : ℕ) (a : coefficientField (K := K) Y) :
    (D : E → E)^[n] (algebraMap (coefficientField (K := K) Y) E a) =
      algebraMap (coefficientField (K := K) Y) E ((coefficientPartial Y hY 0 : _ → _)^[n] a) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih,
      parameter_coefficient_partial_compatible_with_ambient Y hY D hD]

/-- An actual coefficient algebraic over the original parameter and
with vanishing (N+1)st ambient derivative is an original-field polynomial
of degree at most N in that parameter. Its stable curve field, exact
constants and every integration constant are constructed internally. -/
theorem algebraic_parameter_nilpotent_derivative_constructs_polynomial [IsAlgClosed K]
    (D : Derivation K E E) (t : E) (ht : D t = 1) (x : E)
    (hx : IsAlgebraic (IntermediateField.adjoin K ({t} : Set E)) x)
    (N : ℕ) (hzero : (D : E → E)^[N + 1] x = 0) :
    ∃ P : Polynomial K, P.natDegree ≤ N ∧ x = Polynomial.aeval t P := by
  have httrans : Transcendental K t := by
    intro ha
    have hz := derivation_zero_of_isAlgebraic D t ha
    exact one_ne_zero (ht.symm.trans hz)
  let Y : Fin 1 → E := fun _ => t
  have hY : AlgebraicIndependent K Y :=
    (algebraicIndependent_singleton_iff (R := K) (x := Y) (0 : Fin 1)).mpr httrans
  let C := coefficientField (K := K) Y
  let δ := coefficientPartial Y hY 0
  let τ : C := coefficientCoordinate (K := K) Y 0
  have hτ : δ τ = 1 := by
    simpa only [δ, τ, coefficientCoordinate, ite_true] using coefficientPartial_coordinate Y hY 0 0
  have hrange : Set.range Y = ({t} : Set E) := by ext z; simp [Y]
  have hxC : x ∈ C := by
    apply mem_algebraicClosure_iff.mpr
    change IsAlgebraic (IntermediateField.adjoin K (Set.range Y)) x
    rw [hrange]
    exact hx
  let a : C := ⟨x, hxC⟩
  have hz : (δ : C → C)^[N + 1] a = 0 := by
    apply (algebraMap C E).injective
    rw [map_zero]
    exact (parameter_coefficient_partial_iterate_compatible Y hY D ht (N + 1) a).symm.trans hzero
  have htr : Algebra.trdeg K C ≤ 1 := (independent_output_coefficientField_absolute_trdeg Y hY).le
  obtain ⟨P, hdegree, hvalue⟩ := curve_nilpotent_coordinate_derivative_constructs_polynomial δ τ hτ htr N a hz
  refine ⟨P, hdegree, ?_⟩
  calc
    x = algebraMap C E a := rfl
    _ = algebraMap C E (Polynomial.aeval τ P) := congrArg (algebraMap C E) hvalue
    _ = Polynomial.aeval t P :=
      (Polynomial.aeval_algHom_apply (IsScalarTower.toAlgHom K C E) τ P).symm

end DimensionFourDependence
