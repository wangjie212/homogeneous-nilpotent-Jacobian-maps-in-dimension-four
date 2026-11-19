import DimensionFourDependence.ActualGaussPolynomialParameter
import DimensionFourDependence.ConstantReciprocalParameterEquiv

/-! # A polynomial parameter on the same actual closed Gauss cover

The constant reciprocal change is transported through the original
Gauss-cover equivalence. Changing all ternary coefficients by the
inverse equivalence preserves the entire homogeneous forms and their
original source values. The resulting parameter is polynomial in the
original vertex coordinate over the actual transverse field.
-/

namespace DimensionFourDependence

open MvPolynomial

set_option quotPrecheck false
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 100000

variable {K : Type*} [Field K]
    (H : Fin 4 → MvPolynomial (Fin 4) K) (I : ImageRelationWitness H)

local notation "S₀" => FractionRing (MvPolynomial (Fin 4) K)
local notation "L₀" => transverseSourceField K
local notation "w₀" => rationalCoordinate (K := K) (Fin.last 3)

/-- The inverse coefficient change exactly preserves the original
realization of every rational Gauss coefficient in the source field. -/
theorem closed_gauss_parameter_change_coefficient_realization
    (e : RatFunc K ≃ₐ[K] closedGaussParameterField H I)
    (v : RatFunc K ≃ₐ[K] RatFunc K) (r : RatFunc K) :
    closedGaussParameterSourceHom H I (v.trans e) (v.symm r) =
      closedGaussParameterSourceHom H I e r := by
  change ((e (v (v.symm r))) : S₀) = (e r : S₀)
  rw [v.apply_symm_apply]

/-- A constant reciprocal automorphism has precisely the prescribed
changed parameter value in the original source field. -/
theorem closed_gauss_constant_reciprocal_parameter_source_value
    (e : RatFunc K ≃ₐ[K] closedGaussParameterField H I) (a : K) :
    closedGaussParameterSourceHom H I ((constantReciprocalParameterEquiv a).trans e) RatFunc.X =
      (closedGaussParameterSourceHom H I e RatFunc.X - algebraMap K S₀ a)⁻¹ := by
  change closedGaussParameterSourceHom H I e (constantReciprocalParameterEquiv a RatFunc.X) = _
  rw [constantReciprocalParameterEquiv_X, map_inv₀, map_sub, AlgHom.commutes]

/-- Transporting every coefficient of a ternary form by the inverse
parameter equivalence preserves its full actual source value. -/
theorem ternary_form_parameter_change_preserves_source_value
    (e : RatFunc K ≃ₐ[K] closedGaussParameterField H I)
    (v : RatFunc K ≃ₐ[K] RatFunc K) (Q : MvPolynomial (Fin 3) (RatFunc K)) :
    MvPolynomial.eval₂ (closedGaussParameterSourceHom H I (v.trans e)).toRingHom
      (fun j : Fin 3 => rationalCoordinate (K := K) j.castSucc)
      (MvPolynomial.map v.symm.toRingHom Q) =
    MvPolynomial.eval₂ (closedGaussParameterSourceHom H I e).toRingHom
      (fun j : Fin 3 => rationalCoordinate (K := K) j.castSucc) Q := by
  rw [MvPolynomial.eval₂_map]
  have hc : (closedGaussParameterSourceHom H I (v.trans e)).toRingHom.comp v.symm.toRingHom =
      (closedGaussParameterSourceHom H I e).toRingHom := by
    apply RingHom.ext
    intro r
    exact closed_gauss_parameter_change_coefficient_realization H I e v r
  rw [hc]

variable [CharZero K] [IsAlgClosed K]

/-- The original reduced pencil and actual homogeneous ternary forms
construct a constant change of the same entire Gauss cover, homogeneous
changed forms with exact original map values, and a nonconstant polynomial
vertex parameter realizing that changed cover. -/
theorem actual_gauss_forms_construct_polynomial_parameter_on_same_closed_cover
    (e : RatFunc K ≃ₐ[K] closedGaussParameterField H I)
    (p q : MvPolynomial (Fin 4) K) (hp0 : p ≠ 0) (hq0 : q ≠ 0) (hrel : IsRelPrime p q)
    {a b : ℕ} (hp : p.IsHomogeneous a) (hq : q.IsHomogeneous b)
    (hparameter : closedGaussParameterSourceHom H I e RatFunc.X =
      algebraMap (MvPolynomial (Fin 4) K) S₀ p / algebraMap (MvPolynomial (Fin 4) K) S₀ q)
    (hvertex : 0 < p.degreeOf (Fin.last 3) ∨ 0 < q.degreeOf (Fin.last 3))
    (Q : Fin 4 → MvPolynomial (Fin 3) (RatFunc K)) {d : ℕ}
    (hQhom : ∀ i, (Q i).IsHomogeneous d)
    (hQ : ∀ i, MvPolynomial.eval₂ (closedGaussParameterSourceHom H I e).toRingHom
      (fun j : Fin 3 => rationalCoordinate (K := K) j.castSucc) (Q i) =
        algebraMap (MvPolynomial (Fin 4) K) S₀ (H i)) :
    ∃ v : RatFunc K ≃ₐ[K] RatFunc K,
      (v = AlgEquiv.refl ∨ ∃ c : K, v = constantReciprocalParameterEquiv c) ∧
      ∃ (Q' : Fin 4 → MvPolynomial (Fin 3) (RatFunc K)) (U : Polynomial L₀),
        (∀ i, Q' i = MvPolynomial.map v.symm.toRingHom (Q i) ∧ (Q' i).IsHomogeneous d ∧
          MvPolynomial.eval₂ (closedGaussParameterSourceHom H I (v.trans e)).toRingHom
            (fun j : Fin 3 => rationalCoordinate (K := K) j.castSucc) (Q' i) =
              algebraMap (MvPolynomial (Fin 4) K) S₀ (H i)) ∧
        0 < U.natDegree ∧ Polynomial.aeval w₀ U =
          closedGaussParameterSourceHom H I (v.trans e) RatFunc.X := by
  obtain ⟨U, hUdegree, hU⟩ := actual_gauss_ternary_forms_construct_polynomial_parameter_after_constant_change
    H I e p q hp0 hq0 hrel hp hq hparameter hvertex Q hQ
  have hex : ∃ v : RatFunc K ≃ₐ[K] RatFunc K,
      (v = AlgEquiv.refl ∨ ∃ c : K, v = constantReciprocalParameterEquiv c) ∧
      Polynomial.aeval w₀ U = closedGaussParameterSourceHom H I (v.trans e) RatFunc.X := by
    rcases hU with hU | ⟨c, hU⟩
    · exact ⟨AlgEquiv.refl, Or.inl rfl, hU⟩
    · refine ⟨constantReciprocalParameterEquiv c, Or.inr ⟨c, rfl⟩, ?_⟩
      rw [closed_gauss_constant_reciprocal_parameter_source_value]
      exact hU
  obtain ⟨v, hv, hU⟩ := hex
  refine ⟨v, hv, fun i => MvPolynomial.map v.symm.toRingHom (Q i), U, ?_, hUdegree, hU⟩
  intro i
  exact ⟨rfl, (hQhom i).map v.symm.toRingHom,
    (ternary_form_parameter_change_preserves_source_value H I e v (Q i)).trans (hQ i)⟩

end DimensionFourDependence
