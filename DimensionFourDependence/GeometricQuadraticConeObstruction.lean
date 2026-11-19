import DimensionFourDependence.GeometricAffineConeTrace
import DimensionFourDependence.QuadraticConeTraceExclusion

/-! # The actual geometric cone excludes every affine quadratic graph parameter

The original cone construction yields its actual affine chart coordinate
identities and nilpotent trace. The complete quadratic trace comparison
now forbids any affine rescaling of w-Q(x,z) with nonzero quadratic part.
This retains the original constructed parameter and conjugate map; the
missing geometric tangent-field argument must still produce this shape.
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

/-- The specified original geometric cone and fiber data construct the
same complete affine presentation, and its actual polynomial parameter
cannot be an affine rescaling of a quadratic graph with nonzero quadratic
part. The final trace and nilpotent-row exclusion is derived internally. -/
theorem geometric_fixed_vertex_cone_excludes_affine_quadratic_graph_parameter
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
      ∃ (T S : Matrix (Fin 3) (Fin 3) K)
        (hTS : vertexPreservingMatrix T * vertexPreservingMatrix S = 1)
        (hST : vertexPreservingMatrix S * vertexPreservingMatrix T = 1)
        (τ : S₀),
        τ = matrixSourceFractionEquiv (vertexPreservingMatrix T) (vertexPreservingMatrix S) hTS hST
          (closedGaussParameterSourceHom H I (v.trans e) RatFunc.X) ∧
        Transcendental K τ ∧
        linearPolynomialPullback (vertexPreservingMatrix T) (X (Fin.last 3)) = X (Fin.last 3) ∧
        IsHomogMap (linearPolynomialConjugate (vertexPreservingMatrix T) (vertexPreservingMatrix S) H) d ∧
        IsNilpotent (jac (linearPolynomialConjugate (vertexPreservingMatrix T) (vertexPreservingMatrix S) H)) ∧
        polyRank (jac (linearPolynomialConjugate (vertexPreservingMatrix T) (vertexPreservingMatrix S) H)) = 3 ∧
        ¬ ComponentsDependent (linearPolynomialConjugate (vertexPreservingMatrix T) (vertexPreservingMatrix S) H) ∧
        ∃ (a₀ b₀ : Fin 3 → Polynomial K) (P₀ : MvPolynomial (Fin 3) K),
          (∃ i, 0 < (a₀ i).natDegree) ∧ 0 < P₀.totalDegree ∧ P₀.totalDegree ≤ d ∧
          τ = aeval
            ![rationalCoordinate (K := K) (0 : Fin 4) / rationalCoordinate (K := K) (1 : Fin 4),
              rationalCoordinate (K := K) (2 : Fin 4) / rationalCoordinate (K := K) (1 : Fin 4),
              rationalCoordinate (K := K) (3 : Fin 4) / rationalCoordinate (K := K) (1 : Fin 4)] P₀ ∧
          (∀ i : Fin 3, algebraMap (MvPolynomial (Fin 4) K) S₀
            (linearPolynomialConjugate (vertexPreservingMatrix T) (vertexPreservingMatrix S) H i.castSucc) =
              Polynomial.aeval τ (a₀ i) * rationalCoordinate (K := K) (1 : Fin 4) ^ d) ∧
          algebraMap (MvPolynomial (Fin 4) K) S₀
            (linearPolynomialConjugate (vertexPreservingMatrix T) (vertexPreservingMatrix S) H (Fin.last 3)) =
              rationalCoordinate (K := K) (1 : Fin 4) ^ (d - 1) *
                ∑ i : Fin 3, Polynomial.aeval τ (b₀ i) * rationalCoordinate (K := K) i.castSucc ∧
          (∀ i : Fin 3, secondCoordinateAffineChart
            (linearPolynomialConjugate (vertexPreservingMatrix T) (vertexPreservingMatrix S) H i.castSucc) =
              Polynomial.aeval P₀ (a₀ i)) ∧
          secondCoordinateAffineChart
            (linearPolynomialConjugate (vertexPreservingMatrix T) (vertexPreservingMatrix S) H (Fin.last 3)) =
              Polynomial.aeval P₀ (b₀ 0) * X 0 + Polynomial.aeval P₀ (b₀ 1) +
                Polynomial.aeval P₀ (b₀ 2) * X 1 ∧
          affineConeTracePolynomial d P₀ a₀ b₀ = 0 ∧ (a₀ 1).derivative ≠ 0 ∧
          ∀ (a b : K) (Q : MvPolynomial (Fin 2) K), Q.totalDegree ≤ 2 →
            homogeneousComponent 2 Q ≠ 0 →
            P₀ ≠ MvPolynomial.C a * (X 2 - rename Fin.castSucc Q) + MvPolynomial.C b := by
  classical
  obtain ⟨g, hcompat, hg⟩ := geometric_fixed_vertex_cone_constructs_affine_polynomial_forms_and_trace_constraint
    H hd hH hN hrank E P hP hind I s hY h hh e hpara hline p q hp hq hrel hpH hqH hparameter r₀ hr₀ hrvertex
  refine ⟨g, hcompat, ?_⟩
  intro t ht x A w0 B C hx hw ν k hk hdim hinc j hj R hR κ hκ hC V a b hV ha hb hfirst hlast
  obtain ⟨v, hv, T, S, hTS, hST, τ, hτ, htrans, hvertex, hhom, hnil, hrank', hind',
    a₀, b₀, P₀, hnonconstant, hPpositive, hPdegree, hPvalue, hfirst', hlast',
    hchartfirst, hchartlast, htrace, hderivative⟩ :=
    hg t ht x A w0 B C hx hw ν k hk hdim hinc j hj R hR κ hκ hC V a b hV ha hb hfirst hlast
  refine ⟨v, hv, T, S, hTS, hST, τ, hτ, htrans, hvertex, hhom, hnil, hrank', hind',
    a₀, b₀, P₀, hnonconstant, hPpositive, hPdegree, hPvalue, hfirst', hlast',
    hchartfirst, hchartlast, htrace, hderivative, ?_⟩
  intro a b Q hQ hQ₂ hPshape
  apply hind'
  exact (nilpotent_affinely_rescaled_quadratic_parameter_cone_forms_force_dependence
    (linearPolynomialConjugate (vertexPreservingMatrix T) (vertexPreservingMatrix S) H)
      hd hhom hnil P₀ a b Q hQ hQ₂ hPshape a₀ b₀ hchartfirst hchartlast).2

end DimensionFourDependence
