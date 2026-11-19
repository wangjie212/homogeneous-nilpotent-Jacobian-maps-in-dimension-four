import DimensionFourDependence.ActualFixedConeLinearForm
import DimensionFourDependence.LinearPowerFactorUniqueness
import DimensionFourDependence.FixedLinearPowerPolynomialQuotient

/-! # Complete polynomial cone forms with a fixed original linear factor

The original common rational factor and fourth linear quotient survive the
constant parameter change. Comparing one nonzero pure-power coordinate
identifies the changed rational covector up to a scalar with the fixed
original covector. Unit-pivot quotient recovery then constructs all three
fourth-coordinate coefficients over K[t]. All original source values and
the reduced parameter denominator are retained.
-/

namespace DimensionFourDependence

open MvPolynomial

set_option quotPrecheck false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 100000

variable {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]

local notation "S₀" => FractionRing (MvPolynomial (Fin 4) K)
local notation "L₀" => transverseSourceField K
local notation "w₀" => rationalCoordinate (K := K) (Fin.last 3)

omit [CharZero K] [IsAlgClosed K] in
/-- Evaluating a constant polynomial covector gives its actual original
ternary source linear form. -/
theorem fixed_polynomial_parameter_linear_form_source_value
    (t : S₀) (c : Fin 3 → K) :
    MvPolynomial.eval₂ (Polynomial.aeval t).toRingHom
      (fun j : Fin 3 => rationalCoordinate (K := K) j.castSucc)
      (polynomialParameterLinearForm (fun i => Polynomial.C (c i))) =
      algebraMap (MvPolynomial (Fin 4) K) S₀
        (rename Fin.castSucc (linearFormPolynomial c)) := by
  rw [polynomial_parameter_linear_form_source_value]
  simp only [Polynomial.aeval_C, linearFormPolynomial, map_sum, map_mul, rename_C, rename_X]
  simp only [← MvPolynomial.algebraMap_eq,
    ← IsScalarTower.algebraMap_apply K (MvPolynomial (Fin 4) K) S₀, rationalCoordinate]

variable (H : Fin 4 → MvPolynomial (Fin 4) K) (I : ImageRelationWitness H)

/-- The actual complete rational cone forms construct polynomial
coefficients for all four coordinates with one fixed original ternary
linear form. This includes the fourth mixed factor and its entire source
value, the polynomial parameter in the vertex coordinate, and q=γ y^D. -/
theorem actual_complete_rational_cone_forms_construct_fixed_polynomial_forms
    {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d) (hind : ¬ ComponentsDependent H)
    (e : RatFunc K ≃ₐ[K] closedGaussParameterField H I)
    (p q : MvPolynomial (Fin 4) K) (hp0 : p ≠ 0) (hq0 : q ≠ 0) (hrel : IsRelPrime p q)
    {a b : ℕ} (hp : p.IsHomogeneous a) (hq : q.IsHomogeneous b)
    (hparameter : closedGaussParameterSourceHom H I e RatFunc.X =
      algebraMap (MvPolynomial (Fin 4) K) S₀ p / algebraMap (MvPolynomial (Fin 4) K) S₀ q)
    (hvertex : 0 < p.degreeOf (Fin.last 3) ∨ 0 < q.degreeOf (Fin.last 3))
    (Q : Fin 4 → MvPolynomial (Fin 3) (RatFunc K))
    (hQhom : ∀ i, (Q i).IsHomogeneous d)
    (hQ : ∀ i, MvPolynomial.eval₂ (closedGaussParameterSourceHom H I e).toRingHom
      (fun j : Fin 3 => rationalCoordinate (K := K) j.castSucc) (Q i) =
        algebraMap (MvPolynomial (Fin 4) K) S₀ (H i))
    (ℓ₀ : Fin 3 → RatFunc K) (hℓ₀ : ℓ₀ ≠ 0) (r₀ m₀ : Fin 3 → RatFunc K)
    (hfirst : ∀ i : Fin 3, Q i.castSucc = C (r₀ i) * linearFormPolynomial ℓ₀ ^ d)
    (hlast : Q (Fin.last 3) = linearFormPolynomial ℓ₀ ^ (d - 1) * linearFormPolynomial m₀) :
    ∃ v : RatFunc K ≃ₐ[K] RatFunc K,
      (v = AlgEquiv.refl ∨ ∃ c : K, v = constantReciprocalParameterEquiv c) ∧
      ∃ (P : Fin 4 → MvPolynomial (Fin 3) (Polynomial K)) (U : Polynomial L₀)
        (p' : MvPolynomial (Fin 4) K) (q₀ : MvPolynomial (Fin 3) K) (D : ℕ),
        (∀ i, (P i).IsHomogeneous d ∧
          MvPolynomial.map (algebraMap (Polynomial K) (RatFunc K)) (P i) =
            MvPolynomial.map v.symm.toRingHom (Q i) ∧
          MvPolynomial.eval₂ (Polynomial.aeval
            (closedGaussParameterSourceHom H I (v.trans e) RatFunc.X)).toRingHom
            (fun j : Fin 3 => rationalCoordinate (K := K) j.castSucc) (P i) =
              algebraMap (MvPolynomial (Fin 4) K) S₀ (H i)) ∧
        0 < U.natDegree ∧ Polynomial.aeval w₀ U =
          closedGaussParameterSourceHom H I (v.trans e) RatFunc.X ∧
        0 < D ∧ p' ≠ 0 ∧ q₀ ≠ 0 ∧ p'.IsHomogeneous D ∧
        (rename Fin.castSucc q₀).IsHomogeneous D ∧ IsRelPrime p' (rename Fin.castSucc q₀) ∧
        closedGaussParameterSourceHom H I (v.trans e) RatFunc.X =
          algebraMap (MvPolynomial (Fin 4) K) S₀ p' /
            algebraMap (MvPolynomial (Fin 4) K) S₀ (rename Fin.castSucc q₀) ∧
        ∃ (c : Fin 3 → K) (A B : Fin 3 → Polynomial K) (γ : K),
          c ≠ 0 ∧ γ ≠ 0 ∧ q₀ = C γ * linearFormPolynomial c ^ D ∧ D ≤ d ∧
          (∃ i, 0 < (A i).natDegree) ∧
          (∀ i : Fin 3,
            P i.castSucc = C (A i) * polynomialParameterLinearForm (fun j => Polynomial.C (c j)) ^ d ∧
            algebraMap (MvPolynomial (Fin 4) K) S₀ (H i.castSucc) =
              Polynomial.aeval (closedGaussParameterSourceHom H I (v.trans e) RatFunc.X) (A i) *
                (algebraMap (MvPolynomial (Fin 4) K) S₀
                  (rename Fin.castSucc (linearFormPolynomial c))) ^ d) ∧
          P (Fin.last 3) = polynomialParameterLinearForm (fun j => Polynomial.C (c j)) ^ (d - 1) *
            polynomialParameterLinearForm B ∧
          algebraMap (MvPolynomial (Fin 4) K) S₀ (H (Fin.last 3)) =
            (algebraMap (MvPolynomial (Fin 4) K) S₀
              (rename Fin.castSucc (linearFormPolynomial c))) ^ (d - 1) *
              ∑ j : Fin 3, Polynomial.aeval
                (closedGaussParameterSourceHom H I (v.trans e) RatFunc.X) (B j) *
                  rationalCoordinate (K := K) j.castSucc := by
  classical
  obtain ⟨v, hv, P, U, p', q₀, D, hforms, hUdegree, hU, hD, hp', hq₀, hp'hom,
    hq₀hom, hrel', hparameter', ℓ, _hℓ, _hprimitive, _hbase, A, hnonconstant, hfactor⟩ :=
    actual_rational_linear_power_forms_construct_primitive_polynomial_factors H I hH hind
      e p q hp0 hq0 hrel hp hq hparameter hvertex Q hQhom hQ ℓ₀ hℓ₀ r₀ hfirst
  have hfirstvalue (i : Fin 3) : algebraMap (MvPolynomial (Fin 4) K) S₀ (H i.castSucc) =
      Polynomial.aeval (closedGaussParameterSourceHom H I (v.trans e) RatFunc.X) (A i) *
        (MvPolynomial.eval₂ (Polynomial.aeval
          (closedGaussParameterSourceHom H I (v.trans e) RatFunc.X)).toRingHom
          (fun j : Fin 3 => rationalCoordinate (K := K) j.castSucc)
          (polynomialParameterLinearForm ℓ)) ^ d := by
    rw [← (hforms i.castSucc).2.2, hfactor i]
    simp only [MvPolynomial.eval₂_mul, MvPolynomial.eval₂_C, MvPolynomial.eval₂_pow]
    rfl
  obtain ⟨c, hc, hconstant, hDd, γ, hγ, hqpower, hfixedvalue⟩ :=
    actual_polynomial_cone_factor_constructs_fixed_ternary_linear_form H I hd hH hind
      e (v.trans e) p q hp0 hq0 hrel hp hq hparameter hvertex
      p' q₀ hq₀ hD hq₀hom hrel' hparameter' ℓ A hnonconstant hfirstvalue
  have hcov : ℓ = fun j => Polynomial.C (c j) := funext hconstant
  have hfixedpower (i : Fin 3) : P i.castSucc =
      C (A i) * polynomialParameterLinearForm (fun j => Polynomial.C (c j)) ^ d := by
    rw [hfactor i, hcov]
  let aRF : Fin 3 → RatFunc K := fun j => v.symm (ℓ₀ j)
  let bRF : Fin 3 → RatFunc K := fun j => v.symm (m₀ j)
  have hmapFirst (i : Fin 3) :
      MvPolynomial.map (algebraMap (Polynomial K) (RatFunc K)) (P i.castSucc) =
        C (v.symm (r₀ i)) * linearFormPolynomial aRF ^ d := by
    rw [(hforms i.castSucc).2.1, hfirst i]
    simp only [map_mul, MvPolynomial.map_C, map_pow, linearFormPolynomial, map_sum, MvPolynomial.map_X]
    rfl
  have hcovmap : MvPolynomial.map (algebraMap (Polynomial K) (RatFunc K))
      (polynomialParameterLinearForm (fun j => Polynomial.C (c j))) =
        linearFormPolynomial (fun j => algebraMap K (RatFunc K) (c j)) := by
    simp only [polynomialParameterLinearForm, linearFormPolynomial, map_sum, map_mul,
      MvPolynomial.map_C, MvPolynomial.map_X]
    rfl
  have hfieldFirst (i : Fin 3) :
      MvPolynomial.map (algebraMap (Polynomial K) (RatFunc K)) (P i.castSucc) =
        C (algebraMap (Polynomial K) (RatFunc K) (A i)) *
          linearFormPolynomial (fun j => algebraMap K (RatFunc K) (c j)) ^ d := by
    rw [hfixedpower i, map_mul, MvPolynomial.map_C, map_pow, hcovmap]
  have hA0 : A 0 ≠ 0 := by
    intro hz
    apply (linearIndependent_of_componentsIndependent H hind).ne_zero 0
    apply IsFractionRing.injective (MvPolynomial (Fin 4) K) S₀
    have he := hfixedvalue 0
    simpa only [show (0 : Fin 3).castSucc = (0 : Fin 4) by decide,
      hz, map_zero, zero_mul] using he
  obtain ⟨j, hj⟩ : ∃ j, c j ≠ 0 := by
    simpa only [ne_eq, _root_.funext_iff, Pi.zero_apply, not_forall] using hc
  have hjRF : algebraMap K (RatFunc K) (c j) ≠ 0 := by
    simpa only [map_zero] using (algebraMap K (RatFunc K)).injective.ne hj
  have hβ : algebraMap (Polynomial K) (RatFunc K) (A 0) ≠ 0 := by
    simpa only [map_zero] using (RatFunc.algebraMap_injective K).ne hA0
  obtain ⟨s, _hs, hratio⟩ := equal_nonzero_scaled_linear_powers_covectors_proportional
    hd aRF (fun j => algebraMap K (RatFunc K) (c j))
      (v.symm (r₀ 0)) (algebraMap (Polynomial K) (RatFunc K) (A 0))
      hβ j hjRF ((hmapFirst 0).symm.trans (hfieldFirst 0))
  have hmapLast : MvPolynomial.map (algebraMap (Polynomial K) (RatFunc K)) (P (Fin.last 3)) =
      linearFormPolynomial aRF ^ (d - 1) * linearFormPolynomial bRF := by
    rw [(hforms (Fin.last 3)).2.1, hlast]
    simp only [map_mul, map_pow, linearFormPolynomial, map_sum, MvPolynomial.map_C, MvPolynomial.map_X]
    rfl
  obtain ⟨B, _hB, hlastpoly⟩ := proportional_linear_power_quotient_constructs_polynomial_coefficients
    c hc (P (Fin.last 3)) (d - 1) aRF bRF s hratio hmapLast
  refine ⟨v, hv, P, U, p', q₀, D, hforms, hUdegree, hU, hD, hp', hq₀, hp'hom,
    hq₀hom, hrel', hparameter', c, A, B, γ, hc, hγ, hqpower, hDd, hnonconstant,
    (fun i => ⟨hfixedpower i, hfixedvalue i⟩), hlastpoly, ?_⟩
  rw [← (hforms (Fin.last 3)).2.2, hlastpoly, MvPolynomial.eval₂_mul, MvPolynomial.eval₂_pow,
    fixed_polynomial_parameter_linear_form_source_value, polynomial_parameter_linear_form_source_value]

end DimensionFourDependence
