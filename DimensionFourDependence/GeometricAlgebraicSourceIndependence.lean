import DimensionFourDependence.GeometricClosedGaussEmbedding
import Mathlib.RingTheory.AlgebraicIndependent.AlgebraicClosure

/-! # Every algebraic direction-field branch preserves actual source independence

The actual original reduced pencil constructs its compatible closed
Gauss image field in the geometric constants. Every intermediate
algebraic extension of that same field in those constants preserves
independence of the actual projected source point.
-/

namespace DimensionFourDependence

open MvPolynomial

set_option quotPrecheck false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000

universe u

variable {K : Type u} [Field K] [CharZero K]
    (H : Fin 4 → MvPolynomial (Fin 4) K) (I : ImageRelationWitness H)
    (s : Equiv.Perm (Fin 4))
    (hY : AlgebraicIndependent K (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K)
      (FractionRing (MvPolynomial (Fin 4) K)) (H (s i.castSucc))))
    (h : coefficientField (K := K) (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K)
      (FractionRing (MvPolynomial (Fin 4) K)) (H (s i.castSucc))))
    (hh : (h : FractionRing (MvPolynomial (Fin 4) K)) = algebraMap (MvPolynomial (Fin 4) K)
      (FractionRing (MvPolynomial (Fin 4) K)) (H (s 3)))
    (hrank : polyRank (jac H) = 3)
    (E : Type u) [Field E] [Algebra (polynomialOutputField H) E] [Algebra K E]
    [IsScalarTower K (polynomialOutputField H) E] [IsAlgClosed E]
    (P : Ideal (MvPolynomial (Fin 4) E)) [P.IsPrime]
    (hP : P ∈ (extendCoefficientIdeal E (fiberVanishingIdeal
      (L := polynomialOutputField H) (rationalCoordinate (K := K) (n := 4)))).minimalPrimes)

local notation "S₀" => FractionRing (MvPolynomial (Fin 4) K)
local notation "G₀" => FractionRing (MvPolynomial (Fin 4) E ⧸ P)
local notation "C₀" => closedGaussParameterField H I

include hY hh hrank hP

/-- The actual original pencil constructs its closed parameter-field
realization and projected-source independence over every algebraic
coefficient branch of that same realization. -/
theorem geometric_vertex_pencil_constructs_source_independence_on_algebraic_branches
    (e : RatFunc K ≃ₐ[K] C₀)
    (p q : MvPolynomial (Fin 4) K) (hp0 : p ≠ 0) (hq0 : q ≠ 0) (hrel : IsRelPrime p q)
    {a b : ℕ} (hp : p.IsHomogeneous a) (hq : q.IsHomogeneous b)
    (hparameter : closedGaussParameterSourceHom H I e RatFunc.X =
      algebraMap (MvPolynomial (Fin 4) K) S₀ p / algebraMap (MvPolynomial (Fin 4) K) S₀ q)
    (hvertex : 0 < p.degreeOf (Fin.last 3) ∨ 0 < q.degreeOf (Fin.last 3)) :
    ∃ g : C₀ →ₐ[K] E, ∃ f : S₀ →ₐ[K] G₀,
      (∀ i : Fin 4, f (rationalCoordinate (K := K) i) = primeQuotientCoordinate P i) ∧
      (∀ c : C₀, algebraMap E G₀ (g c) = f (c : S₀)) ∧
      ∀ F : IntermediateField g.fieldRange E,
      Algebra.IsAlgebraic g.fieldRange F →
        AlgebraicIndependent F (fun i : Fin 3 => primeQuotientCoordinate P i.castSucc) := by
  obtain ⟨g, hi, f, hf, hg⟩ :=
    geometric_vertex_pencil_constructs_independent_closed_gauss_realization H I s hY h hh hrank E P hP
      e p q hp0 hq0 hrel hp hq hparameter hvertex
  refine ⟨g, f, hf, hg, ?_⟩
  intro F hF
  let : Algebra.IsAlgebraic g.fieldRange F := hF
  let : IsScalarTower g.fieldRange F G₀ := IsScalarTower.of_algebraMap_eq (by intro a; rfl)
  exact hi.extendScalars F

end DimensionFourDependence
