import DimensionFourDependence.ConstantFieldFactorization
import DimensionFourDependence.RealizedFieldIndependence
import DimensionFourDependence.GeometricParameterCrossRelation

/-! # The entire original closed Gauss field on each actual geometric fiber

The actual source-field embedding sends every closed Gauss coefficient
to an element algebraic over the geometric constants. Their entire
field embedding into those constants is constructed compatibly with
the source, rather than only choosing the parameter value. The actual
transverse source coordinates remain independent over its field range.
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
local notation "Q₀" => fun i => algebraMap (MvPolynomial (Fin 4) K) S₀ (H i)

include hY hh hrank hP

/-- The entire closed Gauss field has a constructed embedding into
the actual geometric constants, compatible with the same source embedding
at every original coefficient and every original source coordinate. -/
theorem geometric_component_constructs_closed_gauss_field_embedding :
    ∃ f : S₀ →ₐ[K] G₀, (∀ i : Fin 4, f (rationalCoordinate (K := K) i) = primeQuotientCoordinate P i) ∧
      ∃ g : C₀ →ₐ[K] E, ∀ c : C₀, algebraMap E G₀ (g c) = f (c : S₀) := by
  let M := polynomialOutputField H
  let G := FractionRing (MvPolynomial (Fin 4) E ⧸ P)
  let mGAlgebra : Algebra M G := inferInstance
  let : SMul M G := mGAlgebra.toSMul
  let : IsScalarTower M E G := inferInstance
  let : IsScalarTower K M G := IsScalarTower.of_algebraMap_eq (by
    intro a
    rw [IsScalarTower.algebraMap_apply K E G, IsScalarTower.algebraMap_apply K M E,
      ← IsScalarTower.algebraMap_apply M E G])
  obtain ⟨f, hf⟩ := exists_fiber_embedding_of_relations_eq
    (rationalCoordinate (K := K) (n := 4)) (primeQuotientCoordinate P)
    (rationalSource_adjoin_coordinates_eq_top M)
    (componentGenericPoint_original_relations (rationalCoordinate (K := K) (n := 4)) P hP)
  have hr : (rationalJacobian (Q₀)).rank = 3 := by
    rw [rationalJacobian_polynomial H]
    exact hrank
  let v : C₀ →ₐ[K] G := (f.restrictScalars K).comp (IsScalarTower.toAlgHom K C₀ S₀)
  have halg (c : C₀) : IsAlgebraic E (v c) := by
    have hmem : (c : S₀) ∈ coefficientField (K := K) (fun i : Fin 3 => (Q₀) (s i.castSucc)) :=
      actual_closed_gauss_field_le_graph_coefficient_field H I s hY h hh c.property
    have hc : IsAlgebraic M (c : S₀) :=
      (fullOutput_algebraic_iff_coefficientField (Q₀) hr s hY (c : S₀)).mpr hmem
    exact (hc.algHom f).tower_top E
  obtain ⟨g, hg⟩ := algebraic_images_construct_constant_field_factorization v halg
  exact ⟨f.restrictScalars K, hf, g, hg⟩

/-- The actual reduced vertex-dependent Gauss pencil constructs a
realized closed parameter field over which its actual geometric
transverse source point is independent. Neither a compatible field
embedding nor source independence is assumed. -/
theorem geometric_vertex_pencil_constructs_independent_closed_gauss_realization
    (e : RatFunc K ≃ₐ[K] C₀)
    (p q : MvPolynomial (Fin 4) K) (hp0 : p ≠ 0) (hq0 : q ≠ 0) (hrel : IsRelPrime p q)
    {a b : ℕ} (hp : p.IsHomogeneous a) (hq : q.IsHomogeneous b)
    (hparameter : closedGaussParameterSourceHom H I e RatFunc.X =
      algebraMap (MvPolynomial (Fin 4) K) S₀ p / algebraMap (MvPolynomial (Fin 4) K) S₀ q)
    (hvertex : 0 < p.degreeOf (Fin.last 3) ∨ 0 < q.degreeOf (Fin.last 3)) :
    ∃ g : C₀ →ₐ[K] E,
      AlgebraicIndependent g.fieldRange (fun i : Fin 3 => primeQuotientCoordinate P i.castSucc) ∧
      ∃ f : S₀ →ₐ[K] G₀, (∀ i : Fin 4, f (rationalCoordinate (K := K) i) = primeQuotientCoordinate P i) ∧
        ∀ c : C₀, algebraMap E G₀ (g c) = f (c : S₀) := by
  obtain ⟨f, hf, g, hg⟩ := geometric_component_constructs_closed_gauss_field_embedding H I s hY h hh hrank E P hP
  let : IsScalarTower g.fieldRange E G₀ := IsScalarTower.of_algebraMap_eq (by intro a; rfl)
  have hi := actual_closed_gauss_vertex_pencil_transverse_source_independent H I e p q hp0 hq0 hrel
    hp hq hparameter hvertex
  have hmap := independent_source_coordinates_over_realized_coefficient_field g f hg
    (fun i : Fin 3 => rationalCoordinate (K := K) i.castSucc) hi
  have he : (fun i : Fin 3 => f (rationalCoordinate (K := K) i.castSucc)) =
      (fun i : Fin 3 => primeQuotientCoordinate P i.castSucc) := by funext i; exact hf i.castSucc
  rw [he] at hmap
  exact ⟨g, hmap, f, hf, hg⟩

end DimensionFourDependence
