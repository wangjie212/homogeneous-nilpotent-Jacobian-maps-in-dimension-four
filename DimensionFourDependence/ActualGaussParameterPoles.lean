import DimensionFourDependence.ActualVertexPolynomialChart
import DimensionFourDependence.GenericParameterPole
import DimensionFourDependence.RationalGaussCoefficientDescent

/-! # Constant poles of the original map's actual Gauss parameter forms

For the original vertex-dependent reduced pencil, the parameter is
nonscalar over its actual transverse field. Each descended ternary form
constructs a reduced polynomial coefficient denominator. All its constant
roots yield nonconstant polynomial reciprocal parameters in the original
vertex coordinate; any two such roots, across all four map coordinates,
are equal. Neither source-coordinate field models, generic-pole
persistence nor pullback polynomiality are supplied as hypotheses.
-/

namespace DimensionFourDependence

open MvPolynomial

set_option quotPrecheck false
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 100000

variable {K : Type*} [Field K] [CharZero K]
    (H : Fin 4 → MvPolynomial (Fin 4) K) (I : ImageRelationWitness H)

local notation "S₀" => FractionRing (MvPolynomial (Fin 4) K)
local notation "L₀" => transverseSourceField K
local notation "w₀" => rationalCoordinate (K := K) (Fin.last 3)

/-- The original pencil and actual ternary map values construct reduced
coefficient denominators and polynomial reciprocals at their constant
poles. Every finite constant pole of any of the four coordinate forms
is the same point of the original parameter line. -/
theorem actual_gauss_ternary_forms_construct_unique_constant_pole_pullbacks
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
    ∃ (D : Fin 4 → Polynomial K) (N : Fin 4 → MvPolynomial (Fin 3) (Polynomial K)),
      (∀ i, D i ≠ 0 ∧
        MvPolynomial.map (algebraMap (Polynomial K) (RatFunc K)) (N i) =
          C (algebraMap (Polynomial K) (RatFunc K) (D i)) * Q i ∧
        ∀ c : K, (D i).eval c = 0 → ∃ U : Polynomial L₀, 0 < U.natDegree ∧
          Polynomial.aeval w₀ U =
            (closedGaussParameterSourceHom H I e RatFunc.X - algebraMap K S₀ c)⁻¹) ∧
      (∀ (i j : Fin 4) (c c' : K), (D i).eval c = 0 → (D j).eval c' = 0 → c = c') := by
  classical
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
  have hvalue (i : Fin 4) : MvPolynomial.eval₂ f.toRingHom
      (fun j => algebraMap L₀ S₀ (transverseSourceCoordinate K j)) (Q i) =
      algebraMap (Polynomial L₀) S₀ (sourceVertexPolynomial K (H i)) := by
    change MvPolynomial.eval₂ f.toRingHom
      (fun j : Fin 3 => rationalCoordinate (K := K) j.castSucc) (Q i) =
      Polynomial.aeval w₀ (sourceVertexPolynomial K (H i))
    rw [sourceVertexPolynomial_value]
    exact hQ i
  have hdata (i : Fin 4) := generic_parameter_form_constructs_reduced_pole_pullback
    (transverseSourceCoordinate K) (transverseSourceCoordinate_algebraicIndependent K)
    f ht (Q i) (sourceVertexPolynomial K (H i)) (hvalue i)
  choose D hD N hN hpole using hdata
  refine ⟨D, N, ?_, ?_⟩
  · intro i
    exact ⟨hD i, hN i, hpole i⟩
  · intro i j c c' hc hc'
    by_contra hcc
    obtain ⟨U, _hUdeg, hU⟩ := hpole i c hc
    obtain ⟨V, _hVdeg, hV⟩ := hpole j c' hc'
    have hca : f RatFunc.X ≠ algebraMap L₀ S₀ (algebraMap K L₀ c) := fun h => ht ⟨_, h.symm⟩
    have hcb : f RatFunc.X ≠ algebraMap L₀ S₀ (algebraMap K L₀ c') := fun h => ht ⟨_, h.symm⟩
    have hU' : algebraMap (Polynomial L₀) S₀ U =
        (f RatFunc.X - algebraMap L₀ S₀ (algebraMap K L₀ c))⁻¹ := by
      simpa only [← IsScalarTower.algebraMap_apply K L₀ S₀] using hU
    have hV' : algebraMap (Polynomial L₀) S₀ V =
        (f RatFunc.X - algebraMap L₀ S₀ (algebraMap K L₀ c'))⁻¹ := by
      simpa only [← IsScalarTower.algebraMap_apply K L₀ S₀] using hV
    exact ht (two_distinct_regular_reciprocals_force_scalar (f RatFunc.X)
      (algebraMap K L₀ c) (algebraMap K L₀ c') ((algebraMap K L₀).injective.ne hcc)
      hca hcb U V hU' hV')

end DimensionFourDependence
