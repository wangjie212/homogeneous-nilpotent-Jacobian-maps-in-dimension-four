import DimensionFourDependence.RealizedPolynomialDescent
import DimensionFourDependence.RationalGaussCoefficientDescent

/-! # Actual geometric ternary forms descend through the same Gauss realization

The original reduced pencil supplies source independence and relative
closedness. A compatible actual source embedding and full closed Gauss
embedding determine the coefficient action on every algebraic branch in
the geometric constants. Ternary forms on that branch descend to K(t)
with both their entire branch values and original source values retained.
-/

namespace DimensionFourDependence

open MvPolynomial

set_option quotPrecheck false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000

universe u

variable {K : Type u} [Field K] [CharZero K]
    (H : Fin 4 → MvPolynomial (Fin 4) K) (I : ImageRelationWitness H)
    (E G : Type u) [Field E] [Field G] [Algebra K E] [Algebra K G] [Algebra E G]

local notation "C₀" => closedGaussParameterField H I
local notation "S₀" => FractionRing (MvPolynomial (Fin 4) K)

/-- On every actual algebraic coefficient branch of a compatible
Gauss realization, the original map's ternary expansions descend to
the actual rational parameter field. No additional scalar actions,
relative-closedness or independence hypotheses are supplied. -/
theorem compatible_realized_gauss_ternary_forms_descend_to_parameter
    (g : C₀ →ₐ[K] E) (f : S₀ →ₐ[K] G)
    (hcomp : ∀ c : C₀, algebraMap E G (g c) = f (c : S₀))
    (F : IntermediateField g.fieldRange E) (hF : Algebra.IsAlgebraic g.fieldRange F)
    (e : RatFunc K ≃ₐ[K] C₀)
    (p q : MvPolynomial (Fin 4) K) (hp0 : p ≠ 0) (hq0 : q ≠ 0) (hrel : IsRelPrime p q)
    {a b : ℕ} (hp : p.IsHomogeneous a) (hq : q.IsHomogeneous b)
    (hparameter : closedGaussParameterSourceHom H I e RatFunc.X =
      algebraMap (MvPolynomial (Fin 4) K) S₀ p / algebraMap (MvPolynomial (Fin 4) K) S₀ q)
    (hvertex : 0 < p.degreeOf (Fin.last 3) ∨ 0 < q.degreeOf (Fin.last 3))
    (P : Fin 4 → MvPolynomial (Fin 3) F) {d : ℕ} (hP : ∀ i, (P i).IsHomogeneous d)
    (hvalue : ∀ i : Fin 4,
      aeval (fun j : Fin 3 => f (rationalCoordinate (K := K) j.castSucc)) (P i) =
        f (algebraMap (MvPolynomial (Fin 4) K) S₀ (H i))) :
    ∃ Q : Fin 4 → MvPolynomial (Fin 3) (RatFunc K), ∀ i,
      MvPolynomial.map (((algebraMap g.fieldRange F).comp g.equivFieldRange.toRingHom).comp e.toRingHom) (Q i) = P i ∧
      (Q i).IsHomogeneous d ∧
      MvPolynomial.eval₂ (closedGaussParameterSourceHom H I e).toRingHom
        (fun j : Fin 3 => rationalCoordinate (K := K) j.castSucc) (Q i) =
          algebraMap (MvPolynomial (Fin 4) K) S₀ (H i) := by
  classical
  let : CharZero C₀ := charZero_of_injective_algebraMap (algebraMap K C₀).injective
  let cF : C₀ →+* F := (algebraMap g.fieldRange F).comp g.equivFieldRange.toRingHom
  have hi := actual_closed_gauss_vertex_pencil_transverse_source_independent H I e p q hp0 hq0 hrel
    hp hq hparameter hvertex
  have hex (i : Fin 4) : ∃ R : MvPolynomial (Fin 3) C₀,
      MvPolynomial.map cF R = P i ∧
      aeval (fun j : Fin 3 => rationalCoordinate (K := K) j.castSucc) R =
        algebraMap (MvPolynomial (Fin 4) K) S₀ (H i) := by
    exact compatible_realized_polynomial_expansion_descends g f hcomp F hF
      (closedGaussParameterField_relatively_closed H I) _ hi (P i) _ (hvalue i)
  choose R hR using hex
  refine ⟨fun i => MvPolynomial.map e.symm.toRingHom (R i), ?_⟩
  intro i
  have hback : MvPolynomial.map e.toRingHom (MvPolynomial.map e.symm.toRingHom (R i)) = R i := by
    rw [MvPolynomial.map_map]
    have he : e.toRingHom.comp e.symm.toRingHom = RingHom.id C₀ := by
      apply RingHom.ext
      intro c
      change e (e.symm c) = c
      exact e.apply_symm_apply c
    rw [he, MvPolynomial.map_id]
  have hext := congrArg (MvPolynomial.map cF) hback
  rw [MvPolynomial.map_map] at hext
  have hhom : (R i).IsHomogeneous d := IsHomogeneous.of_map cF.injective
    (by rw [(hR i).1]; exact hP i)
  refine ⟨hext.trans (hR i).1, hhom.map e.symm.toRingHom, ?_⟩
  rw [closed_gauss_rational_ternary_polynomial_source_value H I e (R i), (hR i).2]

end DimensionFourDependence
