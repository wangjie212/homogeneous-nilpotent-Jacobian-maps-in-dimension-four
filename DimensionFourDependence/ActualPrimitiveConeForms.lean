import DimensionFourDependence.ActualPolynomialGaussForms
import DimensionFourDependence.PrimitivePolynomialLinearPowerFamily
import DimensionFourDependence.PrimitiveMapDegree

/-! # The original cone forms have primitive polynomial linear and scalar factors

A common rational linear power is transported through the constructed
constant parameter change. Its normalized polynomial covector is primitive
and has no finite base point, and every scalar factor is polynomial.
Independence of the original map coordinates forces one scalar factor
nonconstant. The actual parameter cover, source quotient and all four
coordinate values from the preceding construction are retained.
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

omit [CharZero K] [IsAlgClosed K] in
/-- A common linear-power family representing independent original
map coordinates has a nonconstant polynomial scalar factor. -/
theorem independent_original_outputs_polynomial_scalar_nonconstant
    (hind : ¬ ComponentsDependent H) (t l : S₀) (d : ℕ) (A : Fin 3 → Polynomial K)
    (hfirst : ∀ i : Fin 3, algebraMap (MvPolynomial (Fin 4) K) S₀ (H i.castSucc) =
      Polynomial.aeval t (A i) * l ^ d) :
    ∃ i, 0 < (A i).natDegree := by
  classical
  by_contra! hzero
  have hC (i : Fin 3) : A i = Polynomial.C ((A i).coeff 0) :=
    Polynomial.eq_C_of_natDegree_eq_zero (Nat.eq_zero_of_le_zero (hzero i))
  have hv (i : Fin 3) : algebraMap (MvPolynomial (Fin 4) K) S₀ (H i.castSucc) =
      algebraMap K S₀ ((A i).coeff 0) * l ^ d := by
    rw [hfirst, hC, Polynomial.aeval_C]
    simp only [Polynomial.coeff_C, ite_true]
  have hv0 : algebraMap (MvPolynomial (Fin 4) K) S₀ (H 0) =
      algebraMap K S₀ ((A 0).coeff 0) * l ^ d := by
    simpa only [show (0 : Fin 3).castSucc = (0 : Fin 4) by decide] using hv 0
  have hv1 : algebraMap (MvPolynomial (Fin 4) K) S₀ (H 1) =
      algebraMap K S₀ ((A 1).coeff 0) * l ^ d := by
    simpa only [show (1 : Fin 3).castSucc = (1 : Fin 4) by decide] using hv 1
  have hA0 : (A 0).coeff 0 ≠ 0 := by
    intro hz
    apply (linearIndependent_of_componentsIndependent H hind).ne_zero 0
    apply IsFractionRing.injective (MvPolynomial (Fin 4) K) S₀
    have he := hv0
    simpa only [hz, map_zero, zero_mul] using he
  have hrel : ((A 1).coeff 0) • H 0 - ((A 0).coeff 0) • H 1 = 0 := by
    apply IsFractionRing.injective (MvPolynomial (Fin 4) K) S₀
    simp only [map_sub, map_zero, smul_eq_C_mul, map_mul, ← MvPolynomial.algebraMap_eq,
      ← IsScalarTower.algebraMap_apply K (MvPolynomial (Fin 4) K) S₀]
    rw [hv0, hv1]
    ring
  apply hind
  let c : Fin 4 → K := Pi.single 0 ((A 1).coeff 0) - Pi.single 1 ((A 0).coeff 0)
  refine ⟨c, ?_, ?_⟩
  · intro hc
    have he := congrFun hc 1
    have hz : -(A 0).coeff 0 = 0 := by simpa [c, Pi.single_apply] using he
    exact hA0 (neg_eq_zero.mp hz)
  · simpa [c, Pi.single_apply, sub_smul, Finset.sum_sub_distrib] using hrel

/-- The original map's common rational linear factor constructs a
primitive polynomial covector, polynomial scalar factors and a nonconstant
scalar member, after the same constant change of the original closed cover. -/
theorem actual_rational_linear_power_forms_construct_primitive_polynomial_factors
    {d : ℕ} (hH : IsHomogMap H d) (hind : ¬ ComponentsDependent H)
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
    (ℓ₀ : Fin 3 → RatFunc K) (hℓ₀ : ℓ₀ ≠ 0) (r₀ : Fin 3 → RatFunc K)
    (hfirst : ∀ i : Fin 3, Q i.castSucc = C (r₀ i) * linearFormPolynomial ℓ₀ ^ d) :
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
        ∃ ℓ : Fin 3 → Polynomial K, ℓ ≠ 0 ∧
          (∀ r : Polynomial K, (∀ i, r ∣ ℓ i) → IsUnit r) ∧
          (∀ c : K, ∃ i, (ℓ i).eval c ≠ 0) ∧
          ∃ A : Fin 3 → Polynomial K, (∃ i, 0 < (A i).natDegree) ∧
            ∀ i : Fin 3, P i.castSucc = C (A i) * polynomialParameterLinearForm ℓ ^ d := by
  classical
  obtain ⟨v, hv, P, U, p', q₀, D, hforms, hUdegree, hU, hD, hp', hq₀, hp'hom, hq₀hom, hrel', hparameter'⟩ :=
    actual_gauss_forms_construct_polynomial_coefficients_and_transverse_denominator
      H I hH e p q hp0 hq0 hrel hp hq hparameter hvertex Q hQhom hQ
  let ℓ' : Fin 3 → RatFunc K := fun j => v.symm (ℓ₀ j)
  have hℓ' : ℓ' ≠ 0 := by
    intro hz
    apply hℓ₀
    funext j
    apply v.symm.injective
    change v.symm (ℓ₀ j) = v.symm 0
    rw [map_zero]
    exact congrFun hz j
  have hpower (i : Fin 3) :
      MvPolynomial.map (algebraMap (Polynomial K) (RatFunc K)) (P i.castSucc) =
      C (v.symm (r₀ i)) * linearFormPolynomial ℓ' ^ d := by
    rw [(hforms i.castSucc).2.1, hfirst i]
    simp only [map_mul, MvPolynomial.map_C, map_pow, linearFormPolynomial, map_sum, MvPolynomial.map_X]
    rfl
  obtain ⟨ℓ, hℓ, hprimitive, hbase, s, A, _hs, _hrep, hA⟩ :=
    rational_linear_power_family_constructs_primitive_polynomial_factors
      (fun i : Fin 3 => P i.castSucc) ℓ' hℓ' (fun i => v.symm (r₀ i)) d hpower
  let l : S₀ := MvPolynomial.eval₂
    (Polynomial.aeval (closedGaussParameterSourceHom H I (v.trans e) RatFunc.X)).toRingHom
    (fun j : Fin 3 => rationalCoordinate (K := K) j.castSucc) (polynomialParameterLinearForm ℓ)
  have hfirstvalue (i : Fin 3) : algebraMap (MvPolynomial (Fin 4) K) S₀ (H i.castSucc) =
      Polynomial.aeval (closedGaussParameterSourceHom H I (v.trans e) RatFunc.X) (A i) * l ^ d := by
    rw [← (hforms i.castSucc).2.2, (hA i).2]
    simp only [MvPolynomial.eval₂_mul, MvPolynomial.eval₂_C, MvPolynomial.eval₂_pow]
    rfl
  have hnonconstant := independent_original_outputs_polynomial_scalar_nonconstant H hind
    (closedGaussParameterSourceHom H I (v.trans e) RatFunc.X) l d A hfirstvalue
  exact ⟨v, hv, P, U, p', q₀, D, hforms, hUdegree, hU, hD, hp', hq₀, hp'hom,
    hq₀hom, hrel', hparameter', ℓ, hℓ, hprimitive, hbase, A, hnonconstant, fun i => (hA i).2⟩

end DimensionFourDependence
