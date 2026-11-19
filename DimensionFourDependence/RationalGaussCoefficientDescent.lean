import DimensionFourDependence.ClosedGaussCoefficientDescent

/-! # Descended ternary coefficients are rational functions of the actual parameter

The original closed Gauss field's specified rational equivalence converts
the descended coefficients to actual elements of K(t). Evaluation uses
the original parameter source homomorphism, and coefficient extension
recovers the entire original algebraic-coefficient expansion exactly.
-/

namespace DimensionFourDependence

open MvPolynomial

set_option quotPrecheck false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000

universe u

variable {K : Type u} [Field K] [CharZero K]
    (H : Fin 4 → MvPolynomial (Fin 4) K) (I : ImageRelationWitness H)

local notation "C₀" => closedGaussParameterField H I
local notation "S₀" => FractionRing (MvPolynomial (Fin 4) K)

/-- Replacing each closed Gauss coefficient by its rational parameter
representative retains its exact value in the original source field. -/
theorem closed_gauss_rational_ternary_polynomial_source_value
    (e : RatFunc K ≃ₐ[K] C₀) (Q : MvPolynomial (Fin 3) C₀) :
    MvPolynomial.eval₂ (closedGaussParameterSourceHom H I e).toRingHom
      (fun i : Fin 3 => rationalCoordinate (K := K) i.castSucc)
      (MvPolynomial.map e.symm.toRingHom Q) =
        aeval (fun i : Fin 3 => rationalCoordinate (K := K) i.castSucc) Q := by
  rw [MvPolynomial.eval₂_map]
  have he : (closedGaussParameterSourceHom H I e).toRingHom.comp e.symm.toRingHom =
      algebraMap C₀ S₀ := by
    ext c
    change ((e (e.symm c) : C₀) : S₀) = (c : S₀)
    rw [AlgEquiv.apply_symm_apply]
  rw [he]
  rfl

variable (E : Type u) [Field E] [Algebra (closedGaussParameterField H I) E] [Algebra.IsAlgebraic (closedGaussParameterField H I) E]
    (G : Type u) [Field G] [Algebra (FractionRing (MvPolynomial (Fin 4) K)) G] [Algebra E G]
    [IsScalarTower (closedGaussParameterField H I) E G]

/-- Every original map entry represented by an algebraic-coefficient
ternary form has an actual ternary form over K(t) of the same degree.
Its specified parameter source value is the original map entry and its
coefficient extension is the entire given expansion. -/
theorem actual_map_ternary_forms_descend_to_rational_gauss_parameter
    (e : RatFunc K ≃ₐ[K] C₀)
    (p q : MvPolynomial (Fin 4) K) (hp0 : p ≠ 0) (hq0 : q ≠ 0) (hrel : IsRelPrime p q)
    {a b : ℕ} (hp : p.IsHomogeneous a) (hq : q.IsHomogeneous b)
    (hparameter : closedGaussParameterSourceHom H I e RatFunc.X =
      algebraMap (MvPolynomial (Fin 4) K) S₀ p / algebraMap (MvPolynomial (Fin 4) K) S₀ q)
    (hvertex : 0 < p.degreeOf (Fin.last 3) ∨ 0 < q.degreeOf (Fin.last 3))
    (P : Fin 4 → MvPolynomial (Fin 3) E) {d : ℕ} (hP : ∀ i, (P i).IsHomogeneous d)
    (hvalue : ∀ i : Fin 4,
      aeval (fun j : Fin 3 => algebraMap S₀ G (rationalCoordinate (K := K) j.castSucc)) (P i) =
        algebraMap S₀ G (algebraMap (MvPolynomial (Fin 4) K) S₀ (H i))) :
    ∃ Q : Fin 4 → MvPolynomial (Fin 3) (RatFunc K), ∀ i,
      MvPolynomial.map ((algebraMap C₀ E).comp e.toRingHom) (Q i) = P i ∧
      (Q i).IsHomogeneous d ∧
      MvPolynomial.eval₂ (closedGaussParameterSourceHom H I e).toRingHom
        (fun j : Fin 3 => rationalCoordinate (K := K) j.castSucc) (Q i) =
          algebraMap (MvPolynomial (Fin 4) K) S₀ (H i) := by
  obtain ⟨Q, hQ⟩ := actual_closed_gauss_ternary_map_coefficients_descend
    H I E G e p q hp0 hq0 hrel hp hq hparameter hvertex P hP hvalue
  refine ⟨fun i => MvPolynomial.map e.symm.toRingHom (Q i), ?_⟩
  intro i
  have hback : MvPolynomial.map e.toRingHom (MvPolynomial.map e.symm.toRingHom (Q i)) = Q i := by
    rw [MvPolynomial.map_map]
    have he : e.toRingHom.comp e.symm.toRingHom = RingHom.id C₀ := by
      apply RingHom.ext
      intro c
      change e (e.symm c) = c
      exact e.apply_symm_apply c
    rw [he, MvPolynomial.map_id]
  have hext := congrArg (MvPolynomial.map (algebraMap C₀ E)) hback
  rw [MvPolynomial.map_map] at hext
  refine ⟨hext.trans (hQ i).1, (hQ i).2.1.map e.symm.toRingHom, ?_⟩
  rw [closed_gauss_rational_ternary_polynomial_source_value H I e (Q i), (hQ i).2.2]

end DimensionFourDependence
