import DimensionFourDependence.ComponentSourceAlgebraicity
import DimensionFourDependence.GeometricClosedGaussEmbedding

/-! # The compatible geometric realization retains algebraic source extension -/

namespace DimensionFourDependence

open MvPolynomial

universe u

set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

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
    [Algebra.IsAlgebraic (polynomialOutputField H) E]
    (P : Ideal (MvPolynomial (Fin 4) E)) [P.IsPrime]
    (hP : P ∈ (extendCoefficientIdeal E (fiberVanishingIdeal
      (L := polynomialOutputField H) (rationalCoordinate (K := K) (n := 4)))).minimalPrimes)

local notation "S₀" => FractionRing (MvPolynomial (Fin 4) K)
local notation "G₀" => FractionRing (MvPolynomial (Fin 4) E ⧸ P)
local notation "C₀" => closedGaussParameterField H I
local notation "Q₀" => fun i => algebraMap (MvPolynomial (Fin 4) K) S₀ (H i)

include hY hh hrank hP

/-- On every actual geometric component over algebraic geometric
constants, the same constructed source and closed Gauss embeddings
make its entire function field algebraic over the original source. -/
theorem geometric_component_constructs_algebraic_source_and_closed_gauss_embedding :
    ∃ f : S₀ →ₐ[K] G₀,
      (∀ i : Fin 4, f (rationalCoordinate (K := K) i) = primeQuotientCoordinate P i) ∧
      ∃ g : C₀ →ₐ[K] E, (∀ c : C₀, algebraMap E G₀ (g c) = f (c : S₀)) ∧
        letI : Algebra S₀ G₀ := f.toRingHom.toAlgebra
        Algebra.IsAlgebraic S₀ G₀ := by
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
  have hgen : IntermediateField.adjoin E
      (Set.range (fun i : Fin 4 => f (rationalCoordinate (K := K) i))) = ⊤ := by
    simpa only [hf] using primeQuotientCoordinate_adjoin_eq_top P
  exact ⟨f.restrictScalars K, hf, g, hg,
    generated_component_isAlgebraic_over_embedded_source f (rationalCoordinate (K := K) (n := 4)) hgen⟩

end DimensionFourDependence
