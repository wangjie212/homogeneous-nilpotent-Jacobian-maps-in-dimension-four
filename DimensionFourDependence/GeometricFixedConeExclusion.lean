import DimensionFourDependence.GeometricAffineLevelIntegrality
import DimensionFourDependence.ConjugatedAffineParabolaObstruction

/-! # The specified actual original cone and nonlinear-fiber data are impossible

The original cone data construct an affine parameter with nonzero vertex
partial. A compatible original source and closed Gauss-field realization
is constructed on the actual geometric fiber. Its unchanged nonzero
quadratic vertex coefficient contradicts that affine parameter after the
actual inverse source change. This closes the final exclusion for the
retained geometric cone hypotheses; their classification remains separate.
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

/-- The same specified original geometric cone and nonlinear parabolic
fiber data now give a contradiction. No tangent field, affine parameter,
constant parameter value or compatible source realization is supplied. -/
theorem geometric_fixed_vertex_cone_data_impossible
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
    False := by
  classical
  obtain ⟨g, hcompat, hg⟩ := geometric_fixed_vertex_cone_constructs_geometrically_integral_affine_level
    H hd hH hN hrank E P hP hind I s hY h hh e hpara hline p q hp hq hrel hpH hqH hparameter r₀ hr₀ hrvertex
  obtain ⟨f₀, hf₀, g₀, hg₀⟩ :=
    geometric_component_constructs_closed_gauss_field_embedding H I s hY h hh hrank E P hP
  refine ⟨g, hcompat, ?_⟩
  intro t ht x A w0 B C hx hw ν k hk hdim hinc j hj R hR κ hκ hC V a b hV ha hb hfirst hlast
  obtain ⟨v, _hv, T, S, hTS, hST, τ, hτ, _htrans, _hclosed, _hvertex, _hhom, _hnil, _hrank', _hind',
    a₀, b₀, P₀, _hnonconstant, _hPpositive, _hPdegree, hPvalue, _hfirst', _hlast',
    _hchartfirst, _hchartlast, _htrace, _hderivative, _hsourcepartial, hpolypartial, _htransverse,
    _hrelation, _hGI, _hglobal, _hgeneric, _hfields, hlinear, _hforced, _hcomposite, _hnoquadratic⟩ :=
    hg t ht x A w0 B C hx hw ν k hk hdim hinc j hj R hR κ hκ hC V a b hV ha hb hfirst hlast
  have hκE : (κ : E) ≠ 0 := by
    intro hz
    exact hκ (Subtype.ext hz)
  have hC0 : C ≠ 0 := by
    rw [hC]
    exact div_ne_zero hκE hR
  have hr : f₀ (closedGaussParameterSourceHom H I (v.trans e) RatFunc.X) =
      algebraMap E G₀ (g₀ ((v.trans e) RatFunc.X)) := by
    exact (hg₀ ((v.trans e) RatFunc.X)).symm
  have hchart : matrixSourceFractionEquiv
      (vertexPreservingMatrix T) (vertexPreservingMatrix S) hTS hST
        (closedGaussParameterSourceHom H I (v.trans e) RatFunc.X) =
      aeval (closedGaussPencilChartPoint (K := K) (finSuccEquiv' (1 : Fin 4))) P₀ := by
    rw [second_coordinate_cone_chart_point]
    exact hτ.symm.trans hPvalue
  exact vertex_preserving_conjugated_affine_parameter_parabola_impossible
    f₀ z₀ hf₀ t ht x A w0 B C hC0 hx hw T S hTS hST
    (closedGaussParameterSourceHom H I (v.trans e) RatFunc.X)
    (g₀ ((v.trans e) RatFunc.X)) hr P₀ (by omega) hpolypartial hchart

end DimensionFourDependence
