import DimensionFourDependence.GeometricConeParameterConstruction
import DimensionFourDependence.ActualPolynomialGaussForms

/-! # Actual cone data construct polynomial Gauss forms and transverse denominator

The same specified fixed-vertex cone and parabolic-fiber data now construct
all four original coordinate forms with K[t] coefficients after a constant
change of the original closed Gauss cover. The new parameter is a polynomial
in the original vertex variable over the actual transverse field, and its
reduced equal-degree homogeneous source quotient has an actual ternary
denominator. No ternary expansion, parameter pole or changed denominator
is supplied as a hypothesis.
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

/-- The actual cone and fiber data construct a polynomial Gauss
parameter, all four original coordinate forms with polynomial parameter
coefficients, and a reduced original quotient with transverse denominator. -/
theorem geometric_fixed_vertex_cone_constructs_polynomial_parameter_forms
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
            algebraMap (MvPolynomial (Fin 4) K) S₀ (rename Fin.castSucc q₀) := by
  classical
  obtain ⟨g, hg⟩ := geometric_fixed_vertex_cone_constructs_rational_parameter_forms
    H hd hH hN hrank E P hP hind I s hY h hh e hpara hline p q hp hq hrel hpH hqH hparameter r₀ hr₀ hrvertex
  refine ⟨g, ?_⟩
  intro t ht x A w0 B C hx hw ν k hk hdim hinc j hj R hR κ hκ hC V a b hV ha hb hfirst hlast
  obtain ⟨Q, hQ⟩ := hg t ht x A w0 B C hx hw ν k hk hdim hinc j hj R hR κ hκ hC
    V a b hV ha hb hfirst hlast
  have hvertex : 0 < p.degreeOf (Fin.last 3) ∨ 0 < q.degreeOf (Fin.last 3) := by
    rcases hr₀ with rfl | rfl
    · exact Or.inl hrvertex
    · exact Or.inr hrvertex
  obtain ⟨v, hv, P', U, p', q₀, D', hforms, hUdegree, hU, hD', hp', hq₀, hp'hom, hq₀hom, hrel', hparameter'⟩ :=
    actual_gauss_forms_construct_polynomial_coefficients_and_transverse_denominator
      H I hH e p q hp hq hrel hpH hqH hparameter hvertex Q
      (fun i => (hQ i).1) (fun i => (hQ i).2)
  refine ⟨v, hv, P', U, p', q₀, D', ?_, hUdegree, hU, hD', hp', hq₀, hp'hom, hq₀hom, hrel', hparameter'⟩
  intro i
  exact ⟨(hforms i).1, (hforms i).2.2⟩

end DimensionFourDependence
