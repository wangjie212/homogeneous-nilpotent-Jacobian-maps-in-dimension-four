import DimensionFourDependence.GeometricCompleteRationalConeForms
import DimensionFourDependence.ActualCompleteFixedConeForms

/-! # Complete fixed polynomial forms from the original geometric cone

The actual specified cone and fiber data construct the coordinate-free
form of (4.10): H_i=y^d A_i(t) for the first three coordinates and
H_4=y^(d-1) sum B_j(t) x_j. The same original closed Gauss parameter
is changed only by the constructed constant reciprocal change. Both
families A and B are polynomial, y is a fixed original ternary linear
form, and the reduced denominator is exactly a scalar times y^D.
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

/-- The actual geometric cone and fiber data construct the complete
fixed polynomial cone presentation, including the fourth mixed factor,
its full original source value, and the exact reduced denominator. -/
theorem geometric_fixed_vertex_cone_constructs_complete_fixed_polynomial_forms
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
      CompatibleGeometricSourceRealization H I P g ∧
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
        ∃ (c : Fin 3 → K) (A B : Fin 3 → Polynomial K) (γ : K),
          c ≠ 0 ∧ γ ≠ 0 ∧ q₀ = MvPolynomial.C γ * linearFormPolynomial c ^ D ∧ D ≤ d ∧
          (∃ i, 0 < (A i).natDegree) ∧
          (∀ i : Fin 3,
            P i.castSucc = MvPolynomial.C (A i) * polynomialParameterLinearForm (fun j => Polynomial.C (c j)) ^ d ∧
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
  obtain ⟨g, hcompat, hg⟩ := geometric_fixed_vertex_cone_constructs_complete_rational_factorization
    H hd hH hN hrank E P hP hind I s hY h hh e hpara hline p q hp hq hrel hpH hqH hparameter r₀ hr₀ hrvertex
  refine ⟨g, hcompat, ?_⟩
  intro t ht x A w0 B C hx hw ν k hk hdim hinc j hj R hR κ hκ hC V a b hV ha hb hfirst hlast
  obtain ⟨Q, hQ, ℓ, hℓ, r, hr, m, hm⟩ :=
    hg t ht x A w0 B C hx hw ν k hk hdim hinc j hj R hR κ hκ hC V a b hV ha hb hfirst hlast
  have hvertex : 0 < p.degreeOf (Fin.last 3) ∨ 0 < q.degreeOf (Fin.last 3) := by
    rcases hr₀ with rfl | rfl
    · exact Or.inl hrvertex
    · exact Or.inr hrvertex
  obtain ⟨v, hv, P', U, p', q₀, D', hforms, hUdegree, hU, hD', hp', hq₀, hp'hom,
    hq₀hom, hrel', hparameter', c, a₀, b₀, γ, hc, hγ, hqpower, hDd, hnonconstant,
    hfirstfixed, hlastpoly, hlastvalue⟩ :=
    actual_complete_rational_cone_forms_construct_fixed_polynomial_forms H I hd hH hind
      e p q hp hq hrel hpH hqH hparameter hvertex Q
      (fun i => (hQ i).1) (fun i => (hQ i).2) ℓ hℓ r m hr hm
  exact ⟨v, hv, P', U, p', q₀, D', (fun i => ⟨(hforms i).1, (hforms i).2.2⟩),
    hUdegree, hU, hD', hp', hq₀, hp'hom, hq₀hom, hrel', hparameter',
    c, a₀, b₀, γ, hc, hγ, hqpower, hDd, hnonconstant, hfirstfixed, hlastpoly, hlastvalue⟩

end DimensionFourDependence
