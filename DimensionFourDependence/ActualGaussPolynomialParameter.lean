import DimensionFourDependence.ActualGaussParameterPoles
import DimensionFourDependence.GaussVertexOutputDependence
import DimensionFourDependence.PolynomialParameterChange

/-! # A polynomial vertex parameter for the original Gauss forms

The original reduced vertex-dependent Gauss pencil forces a nonconstant
original map coordinate. Its descended ternary form, with its exact source
value, constructs a nonconstant polynomial in the original vertex coordinate
representing either the original parameter or a constant translated reciprocal.
The finite-pole and infinity-pole alternatives are both derived.
-/

namespace DimensionFourDependence

open MvPolynomial

set_option quotPrecheck false
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 100000

variable {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]
    (H : Fin 4 → MvPolynomial (Fin 4) K) (I : ImageRelationWitness H)

local notation "S₀" => FractionRing (MvPolynomial (Fin 4) K)
local notation "L₀" => transverseSourceField K
local notation "w₀" => rationalCoordinate (K := K) (Fin.last 3)

/-- Actual descended ternary map forms and the original reduced pencil
construct a nonconstant polynomial vertex parameter after the identity
or a constant reciprocal change. No output vertex-dependence, generic
pole or source-coordinate field presentation is assumed separately. -/
theorem actual_gauss_ternary_forms_construct_polynomial_parameter_after_constant_change
    (e : RatFunc K ≃ₐ[K] closedGaussParameterField H I)
    (p q : MvPolynomial (Fin 4) K) (hp0 : p ≠ 0) (hq0 : q ≠ 0) (hrel : IsRelPrime p q)
    {a b : ℕ} (hp : p.IsHomogeneous a) (hq : q.IsHomogeneous b)
    (hparameter : closedGaussParameterSourceHom H I e RatFunc.X =
      algebraMap (MvPolynomial (Fin 4) K) S₀ p / algebraMap (MvPolynomial (Fin 4) K) S₀ q)
    (hvertex : 0 < p.degreeOf (Fin.last 3) ∨ 0 < q.degreeOf (Fin.last 3))
    (Q : Fin 4 → MvPolynomial (Fin 3) (RatFunc K))
    (hQ : ∀ i, MvPolynomial.eval₂ (closedGaussParameterSourceHom H I e).toRingHom
      (fun j : Fin 3 => rationalCoordinate (K := K) j.castSucc) (Q i) =
        algebraMap (MvPolynomial (Fin 4) K) S₀ (H i)) :
    ∃ U : Polynomial L₀, 0 < U.natDegree ∧
      (Polynomial.aeval w₀ U = closedGaussParameterSourceHom H I e RatFunc.X ∨
        ∃ c : K, Polynomial.aeval w₀ U =
          (closedGaussParameterSourceHom H I e RatFunc.X - algebraMap K S₀ c)⁻¹) := by
  let f := closedGaussParameterSourceHom H I e
  let : Algebra (Polynomial L₀) S₀ := (Polynomial.aeval w₀).toRingHom.toAlgebra
  let : IsScalarTower L₀ (Polynomial L₀) S₀ := IsScalarTower.of_algebraMap_eq
    (by intro c; exact (Polynomial.aeval_C w₀ c).symm)
  let : IsFractionRing (Polynomial L₀) S₀ := actual_source_vertex_polynomial_isFractionRing K
  have htrans := reduced_vertex_parameter_transcendental_over_transverse_field
    p q hp0 hq0 hrel hp hq hvertex
  rw [← hparameter] at htrans
  change Transcendental L₀ (f RatFunc.X) at htrans
  have ht : ¬ ∃ c : L₀, algebraMap L₀ S₀ c = f RatFunc.X := by
    rintro ⟨c, hc⟩
    apply htrans
    rw [← hc]
    exact isAlgebraic_algebraMap (R := L₀) (A := S₀) c
  obtain ⟨i, hi⟩ := reduced_vertex_gauss_parameter_constructs_nonconstant_vertex_output
    H I e p q hp0 hq0 hrel hp hq hparameter hvertex
  have hvalue : MvPolynomial.eval₂ f.toRingHom
      (fun j => algebraMap L₀ S₀ (transverseSourceCoordinate K j)) (Q i) =
      algebraMap (Polynomial L₀) S₀ (sourceVertexPolynomial K (H i)) := by
    change MvPolynomial.eval₂ f.toRingHom
      (fun j : Fin 3 => rationalCoordinate (K := K) j.castSucc) (Q i) =
      Polynomial.aeval w₀ (sourceVertexPolynomial K (H i))
    rw [sourceVertexPolynomial_value]
    exact hQ i
  exact generic_parameter_form_polynomial_after_constant_change
    (transverseSourceCoordinate K) (transverseSourceCoordinate_algebraicIndependent K)
    f ht (Q i) (sourceVertexPolynomial K (H i)) hi hvalue

end DimensionFourDependence
