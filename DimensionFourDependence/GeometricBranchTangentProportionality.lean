import DimensionFourDependence.GeometricAlgebraicSourceIndependence
import DimensionFourDependence.GeometricParameterTangentProportionality

/-! # Finite tangent proportionality without assumed source independence

The actual original reduced pencil constructs its closed Gauss image
field and independence over every algebraic direction-field branch.
The geometric tangent-proportionality calculation therefore needs only
the specified vertex form and quadratic coefficient formula on such a
branch; no field compatibility or source independence is supplied.
-/

namespace DimensionFourDependence

open MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra

set_option quotPrecheck false
set_option maxHeartbeats 2000000
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

/-- The actual original geometric pencil constructs its own closed
Gauss realization and finite tangent proportionality on every algebraic
direction branch. Projected-source independence is derived internally. -/
theorem geometric_vertex_pencil_constructs_tangent_proportionality_on_algebraic_branches
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
    (r : MvPolynomial (Fin 4) K) (hr : r = p ∨ r = q) (hrvertex : 0 < r.degreeOf (Fin.last 3)) :
    ∃ g : closedGaussParameterField H I →ₐ[K] E, ∃ f : S₀ →ₐ[K] G₀,
      (∀ i : Fin 4, f (rationalCoordinate (K := K) i) = z₀ i) ∧
      (∀ c : closedGaussParameterField H I, algebraMap E G₀ (g c) = f (c : S₀)) ∧
      ∀ (F : IntermediateField g.fieldRange E), Algebra.IsAlgebraic g.fieldRange F →
      ∀ (t : G₀), Transcendental E t → ∀ (x : Fin 3 → E) (A : Fin 3 → F) (w0 B C : E),
      (∀ i : Fin 3, z₀ i.castSucc = algebraMap E G₀ (x i) + algebraMap F G₀ (A i) * t) →
      (z₀ (Fin.last 3) = algebraMap E G₀ w0 + algebraMap E G₀ B * t + algebraMap E G₀ C * t ^ 2) →
      ∀ (R : E), R ≠ 0 → ∀ (κ : F), κ ≠ 0 → C = algebraMap F E κ / R →
      ∃ (Φ : MvPolynomial (Fin 3) K) (m : ℕ),
        Φ ≠ 0 ∧ Φ.IsHomogeneous m ∧ 0 < m ∧ Irreducible Φ ∧
        (projectiveFieldPointIdeal (E := K) A).toIdeal = Ideal.span {Φ} ∧
        let T := ∑ i : Fin 3, aeval (fun k => algebraMap F E (A k)) (pderiv i Φ) * x i
        IsAlgebraic F (R / T) ∧ Module.Finite F (IntermediateField.adjoin F {R / T}) ∧
          ∃ u : IntermediateField.adjoin F {R / T}, u ≠ 0 ∧ R = (u : E) * T := by
  have hvertex : 0 < p.degreeOf (Fin.last 3) ∨ 0 < q.degreeOf (Fin.last 3) := by
    rcases hr with rfl | rfl
    · exact Or.inl hrvertex
    · exact Or.inr hrvertex
  obtain ⟨g, f, hf, hg, hi⟩ := geometric_vertex_pencil_constructs_source_independence_on_algebraic_branches
    H I s hY h hh hrank E P hP e p q hp hq hrel hpH hqH hparameter hvertex
  refine ⟨g, f, hf, hg, ?_⟩
  intro F hF t ht x A w0 B C hx hw R hR κ hκ hC
  let : IsScalarTower K F E := IsScalarTower.of_algebraMap_eq (by intro a; rfl)
  have hrhom : r.IsHomogeneous D := by rcases hr with rfl | rfl <;> assumption
  exact geometric_parameter_vertex_constructs_finite_tangent_proportionality H hd hH hN hrank E P hP F
    hind I s hY h hh e hpara hline p q hp hq hrel hparameter r hr hrhom hrvertex
    t ht x A w0 B C hx hw (hi F hF) R hR κ hκ hC

end DimensionFourDependence
