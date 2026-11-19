import DimensionFourDependence.VertexParameterTranscendence
import DimensionFourDependence.RationalParameterDerivation
import DimensionFourDependence.RationalClosedGaussCover

/-! # The original nonzero vertex differential survives any Gauss cover parameter

Every other parameter of the same actual closed Gauss field expresses
the original parameter as a rational function of it. The full rational
chain rule therefore transports nonvanishing from the original reduced
vertex-dependent pencil, without a supplied derivative condition.
-/

namespace DimensionFourDependence

open MvPolynomial

set_option maxHeartbeats 2000000

variable {K : Type*} [Field K] [CharZero K]

/-- Every parameter equivalence of the same actual closed Gauss field
has nonzero source vertex derivative when the original reduced pencil
genuinely depends on that vertex. -/
theorem actual_closed_gauss_changed_parameter_vertex_partial_ne_zero
    (H : Fin 4 → MvPolynomial (Fin 4) K) (I : ImageRelationWitness H)
    (e₀ e : RatFunc K ≃ₐ[K] closedGaussParameterField H I)
    (p q : MvPolynomial (Fin 4) K) (hp0 : p ≠ 0) (hq0 : q ≠ 0) (hrel : IsRelPrime p q)
    {a b : ℕ} (hp : p.IsHomogeneous a) (hq : q.IsHomogeneous b)
    (hparameter : closedGaussParameterSourceHom H I e₀ RatFunc.X =
      algebraMap (MvPolynomial (Fin 4) K) (FractionRing (MvPolynomial (Fin 4) K)) p /
        algebraMap (MvPolynomial (Fin 4) K) (FractionRing (MvPolynomial (Fin 4) K)) q)
    (hvertex : 0 < p.degreeOf (Fin.last 3) ∨ 0 < q.degreeOf (Fin.last 3)) :
    rationalPartial (K := K) (Fin.last 3) (closedGaussParameterSourceHom H I e RatFunc.X) ≠ 0 := by
  have hnonzero := reduced_vertex_parameter_rational_partial_ne_zero
    p q hp0 hq0 hrel hp hq (Fin.last 3) hvertex
  rw [← hparameter] at hnonzero
  let r : RatFunc K := e.symm (e₀ RatFunc.X)
  have hr : closedGaussParameterSourceHom H I e r = closedGaussParameterSourceHom H I e₀ RatFunc.X := by
    change (closedGaussParameterField H I).val (e (e.symm (e₀ RatFunc.X))) = _
    rw [e.apply_symm_apply]
    rfl
  intro hz
  have he := rational_parameter_chain_rule (closedGaussParameterSourceHom H I e)
    (rationalPartial (K := K) (Fin.last 3)) r
  rw [hr, hz, mul_zero] at he
  exact hnonzero he

end DimensionFourDependence
