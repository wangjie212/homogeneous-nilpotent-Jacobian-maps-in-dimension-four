import DimensionFourDependence.GeometricPrimitiveConeForms
import DimensionFourDependence.ActualFixedConeLinearForm

/-! # The actual cone has a fixed ternary source linear factor

The specified geometric cone and fiber data construct their polynomial
parameter forms and primitive factors. Valuative integrality and the
source Euler derivation make the evaluated linear factor an original
homogeneous source linear polynomial. The reduced denominator divides
its power, hence is a scalar times that linear form to its homogeneous
degree. Vertex independence and transverse source independence force
a fixed ternary covector. All original parameter and map values remain.
-/

namespace DimensionFourDependence

open MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra

set_option quotPrecheck false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 100000

universe u

variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]
    (H : Fin 4 → MvPolynomial (Fin 4) K)
    {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d)
    (hN : IsNilpotent (jac H)) (hrank : polyRank (jac H) = 3)
    (E : Type u) [Field E] [Algebra (polynomialOutputField H) E] [Algebra K E]
    [IsScalarTower K (polynomialOutputField H) E]
    [Algebra.IsAlgebraic (polynomialOutputField H) E] [IsAlgClosed E]
    (P : Ideal (MvPolynomial (Fin 4) E)) [P.IsPrime]
    (hP : P ∈ (extendCoefficientIdeal E (fiberVanishingIdeal
      (L := polynomialOutputField H) (rationalCoordinate (K := K) (n := 4)))).minimalPrimes)

local notation "S₀" => FractionRing (MvPolynomial (Fin 4) K)
local notation "G₀" => FractionRing (MvPolynomial (Fin 4) E ⧸ P)
local notation "z₀" => primeQuotientCoordinate P

include hd hH hN hrank hP

/-- The actual geometric cone and fiber data construct the fixed
original ternary source linear form, its exact denominator power, and
the first-three coordinate representation y^d a_i(t) with polynomial
scalar factors and a nonconstant member. -/
theorem geometric_fixed_vertex_cone_constructs_fixed_ternary_linear_factor
    (hind : ¬ ComponentsDependent H) (I : ImageRelationWitness H)
    (s : Equiv.Perm (Fin 4))
    (hY : AlgebraicIndependent K (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K) S₀ (H (s i.castSucc))))
    (h : coefficientField (K := K) (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K) S₀ (H (s i.castSucc))))
    (hh : (h : S₀) = algebraMap (MvPolynomial (Fin 4) K) S₀ (H (s 3)))
    (e : RatFunc K ≃ₐ[K] closedGaussParameterField H I)
    (hpara : LiesInAffineParabola (L := E) z₀) (hline : ¬ LiesInAffineLine (E := E) z₀)
    (p q : MvPolynomial (Fin 4) K) (hp : p ≠ 0) (hq : q ≠ 0) (hrel : IsRelPrime p q)
    {D : ℕ} (hpH : p.IsHomogeneous D) (hqH : q.IsHomogeneous D)
    (hparameter : closedGaussParameterSourceHom H I e RatFunc.X =
      algebraMap (MvPolynomial (Fin 4) K) S₀ p / algebraMap (MvPolynomial (Fin 4) K) S₀ q)
    (r₀ : MvPolynomial (Fin 4) K) (hr₀ : r₀ = p ∨ r₀ = q) (hrvertex : 0 < r₀.degreeOf (Fin.last 3)) :
    ∃ g : closedGaussParameterField H I →ₐ[K] E,
      ∀ (t : G₀), Transcendental E t → ∀ (x A : Fin 3 → E) (w0 B C : E),
      (∀ i : Fin 3, z₀ i.castSucc = algebraMap E G₀ (x i) + algebraMap E G₀ (A i) * t) →
      (z₀ (Fin.last 3) = algebraMap E G₀ w0 + algebraMap E G₀ B * t + algebraMap E G₀ C * t ^ 2) →
      ∀ (ν : Fin 3 → g.fieldRange) (k : Fin 3), ν k ≠ 0 →
      Algebra.trdeg K (projectiveRatioField (K := K) ν k) ≠ 0 →
      (∑ i : Fin 3, (ν i : E) * A i) = 0 → ∀ (j : Fin 3), A j = 1 →
      ∀ (R : E), R ≠ 0 → ∀ (κ : g.fieldRange), κ ≠ 0 → C = (κ : E) / R →
      ∀ (V : Fin 3 → E) (a b : E), (∀ i, IsAlgebraic g.fieldRange (V i)) →
      IsAlgebraic g.fieldRange a → IsAlgebraic g.fieldRange b →
      (∀ i : Fin 3, aeval z₀ (H i.castSucc) = algebraMap E G₀ (V i) * (algebraMap E G₀ R) ^ d) →
      (aeval z₀ (H (Fin.last 3)) = algebraMap E G₀ a * (algebraMap E G₀ R) ^ d +
        algebraMap E G₀ b * (algebraMap E G₀ R) ^ (d - 1) *
          (∑ i : Fin 3, algebraMap E G₀ (ν i : E) * z₀ i.castSucc)) →
    ∃ v : RatFunc K ≃ₐ[K] RatFunc K,
      (v = AlgEquiv.refl ∨ ∃ c : K, v = constantReciprocalParameterEquiv c) ∧
      ∃ (P : Fin 4 → MvPolynomial (Fin 3) (Polynomial K)) (U : Polynomial (transverseSourceField K))
        (p' : MvPolynomial (Fin 4) K) (q₀ : MvPolynomial (Fin 3) K) (D : ℕ),
        (∀ i, (P i).IsHomogeneous d ∧
          MvPolynomial.eval₂ (Polynomial.aeval
            (closedGaussParameterSourceHom H I (v.trans e) RatFunc.X)).toRingHom
            (fun j : Fin 3 => rationalCoordinate (K := K) j.castSucc) (P i) =
              algebraMap (MvPolynomial (Fin 4) K) S₀ (H i)) ∧
        0 < U.natDegree ∧ Polynomial.aeval (rationalCoordinate (K := K) (Fin.last 3)) U =
          closedGaussParameterSourceHom H I (v.trans e) RatFunc.X ∧
        0 < D ∧ p' ≠ 0 ∧ q₀ ≠ 0 ∧ p'.IsHomogeneous D ∧
        (rename Fin.castSucc q₀).IsHomogeneous D ∧ IsRelPrime p' (rename Fin.castSucc q₀) ∧
        closedGaussParameterSourceHom H I (v.trans e) RatFunc.X =
          algebraMap (MvPolynomial (Fin 4) K) S₀ p' /
            algebraMap (MvPolynomial (Fin 4) K) S₀ (rename Fin.castSucc q₀) ∧
        ∃ ℓ : Fin 3 → Polynomial K, ℓ ≠ 0 ∧
          (∀ r : Polynomial K, (∀ i, r ∣ ℓ i) → IsUnit r) ∧
          (∀ c : K, ∃ i, (ℓ i).eval c ≠ 0) ∧
          ∃ a₀ : Fin 3 → Polynomial K, (∃ i, 0 < (a₀ i).natDegree) ∧
            (∀ i : Fin 3, P i.castSucc = MvPolynomial.C (a₀ i) * polynomialParameterLinearForm ℓ ^ d) ∧
            ∃ c : Fin 3 → K, c ≠ 0 ∧ (∀ i, ℓ i = Polynomial.C (c i)) ∧
              D ≤ d ∧ ∃ γ : K, γ ≠ 0 ∧ q₀ = MvPolynomial.C γ * linearFormPolynomial c ^ D ∧
                ∀ i : Fin 3, algebraMap (MvPolynomial (Fin 4) K) S₀ (H i.castSucc) =
                  Polynomial.aeval (closedGaussParameterSourceHom H I (v.trans e) RatFunc.X) (a₀ i) *
                    (algebraMap (MvPolynomial (Fin 4) K) S₀
                      (rename Fin.castSucc (linearFormPolynomial c))) ^ d := by
  classical
  obtain ⟨g, hg⟩ := geometric_fixed_vertex_cone_constructs_primitive_polynomial_linear_factors
    H hd hH hN hrank E P hP hind I s hY h hh e hpara hline p q hp hq hrel hpH hqH hparameter r₀ hr₀ hrvertex
  refine ⟨g, ?_⟩
  intro t ht x A w0 B C hx hw ν k hk hdim hinc j hj R hR κ hκ hC V a b hV ha hb hfirst hlast
  obtain ⟨v, hv, P', U, p', q₀, D', hforms, hUdegree, hU, hD', hp', hq₀, hp'hom, hq₀hom, hrel', hparameter',
    ℓ, hℓ, hprimitive, hbase, a₀, hnonconstant, hfactor⟩ :=
    hg t ht x A w0 B C hx hw ν k hk hdim hinc j hj R hR κ hκ hC V a b hV ha hb hfirst hlast
  have hvertex : 0 < p.degreeOf (Fin.last 3) ∨ 0 < q.degreeOf (Fin.last 3) := by
    rcases hr₀ with rfl | rfl
    · exact Or.inl hrvertex
    · exact Or.inr hrvertex
  have hfirstvalue (i : Fin 3) : algebraMap (MvPolynomial (Fin 4) K) S₀ (H i.castSucc) =
      Polynomial.aeval (closedGaussParameterSourceHom H I (v.trans e) RatFunc.X) (a₀ i) *
        (MvPolynomial.eval₂ (Polynomial.aeval
          (closedGaussParameterSourceHom H I (v.trans e) RatFunc.X)).toRingHom
          (fun j : Fin 3 => rationalCoordinate (K := K) j.castSucc) (polynomialParameterLinearForm ℓ)) ^ d := by
    rw [← (hforms i.castSucc).2, hfactor i]
    simp only [MvPolynomial.eval₂_mul, MvPolynomial.eval₂_C, MvPolynomial.eval₂_pow]
    rfl
  obtain ⟨c, hc, hconstant, hDd, γ, hγ, hqpower, hfirstfixed⟩ :=
    actual_polynomial_cone_factor_constructs_fixed_ternary_linear_form
      H I hd hH hind e (v.trans e) p q hp hq hrel hpH hqH hparameter hvertex
      p' q₀ hq₀ hD' hq₀hom hrel' hparameter' ℓ a₀ hnonconstant hfirstvalue
  exact ⟨v, hv, P', U, p', q₀, D', hforms, hUdegree, hU, hD', hp', hq₀, hp'hom, hq₀hom, hrel', hparameter',
    ℓ, hℓ, hprimitive, hbase, a₀, hnonconstant, hfactor, c, hc, hconstant, hDd, γ, hγ, hqpower, hfirstfixed⟩

end DimensionFourDependence
