import DimensionFourDependence.GenericOutputPoint

/-! # The original polynomial map on an actual generic component

Every component generic point evaluates `H` to the generic value over
`K(H)`. This is obtained from the checked equality of fiber relations.
-/

namespace DimensionFourDependence

open MvPolynomial

variable {K : Type*} [Field K]

/-- Rank three excludes the zero polynomial map. -/
theorem rank_three_polynomial_map_ne_zero
    (H : Fin 4 → MvPolynomial (Fin 4) K) (hrank : polyRank (jac H) = 3) : H ≠ 0 := by
  intro hz
  have hJ : jac H = 0 := by
    funext i j
    change pderiv j (H i) = 0
    rw [hz]
    simp
  have hr0 : polyRank (jac H) = 0 := by rw [hJ]; simp [polyRank]
  omega

/-- Every actual component generic point lies over the full generic output value. -/
theorem geometric_component_generic_output_evaluation
    (H : Fin 4 → MvPolynomial (Fin 4) K) (E : Type*) [Field E]
    [Algebra (polynomialOutputField H) E] [Algebra K E]
    [IsScalarTower K (polynomialOutputField H) E]
    (P : Ideal (MvPolynomial (Fin 4) E)) [P.IsPrime]
    (hP : P ∈ (extendCoefficientIdeal E (fiberVanishingIdeal
      (L := polynomialOutputField H) (rationalCoordinate (K := K) (n := 4)))).minimalPrimes) :
    ∀ i, aeval (primeQuotientCoordinate P) (MvPolynomial.map (algebraMap K E) (H i)) =
      algebraMap E (FractionRing (MvPolynomial (Fin 4) E ⧸ P)) (genericOutputValue H E i) := by
  let M := polynomialOutputField H
  let G := FractionRing (MvPolynomial (Fin 4) E ⧸ P)
  let mGAlgebra : Algebra M G := inferInstance
  let : SMul M G := mGAlgebra.toSMul
  let : IsScalarTower M E G := inferInstance
  let : IsScalarTower K M G := IsScalarTower.of_algebraMap_eq
    (R := K) (S := M) (A := G) (by
      intro c
      rw [IsScalarTower.algebraMap_apply K E G, IsScalarTower.algebraMap_apply K M E,
        ← IsScalarTower.algebraMap_apply M E G])
  obtain ⟨f, hf⟩ := exists_fiber_embedding_of_relations_eq
    (rationalCoordinate (K := K) (n := 4)) (primeQuotientCoordinate P)
    (rationalSource_adjoin_coordinates_eq_top M)
    (componentGenericPoint_original_relations (rationalCoordinate (K := K) (n := 4)) P hP)
  intro i
  rw [aeval_map_coefficients]
  have hev := comp_aeval_apply (rationalCoordinate (K := K) (n := 4)) (f.restrictScalars K) (H i)
  have hev' : f (aeval (rationalCoordinate (K := K) (n := 4)) (H i)) =
      aeval (primeQuotientCoordinate P) (H i) := by
    simpa only [AlgHom.restrictScalars_apply, hf] using hev
  rw [← hev']
  have heq := aeval_polynomial_to_fraction (fun j : Fin 4 => (X j : MvPolynomial (Fin 4) K)) (H i)
  simp only [aeval_X_left_apply] at heq
  change algebraMap (MvPolynomial (Fin 4) K) (FractionRing (MvPolynomial (Fin 4) K)) (H i) =
    aeval (rationalCoordinate (K := K) (n := 4)) (H i) at heq
  rw [← heq]
  change f (algebraMap M (FractionRing (MvPolynomial (Fin 4) K))
    (fullOutputCoordinate (K := K) (fun j => algebraMap (MvPolynomial (Fin 4) K)
      (FractionRing (MvPolynomial (Fin 4) K)) (H j)) i)) = _
  rw [f.commutes]
  exact (IsScalarTower.algebraMap_apply M E G _).symm

end DimensionFourDependence
