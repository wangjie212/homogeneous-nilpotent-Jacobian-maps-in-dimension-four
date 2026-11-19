import DimensionFourDependence.GeometricComponentConjugacy

/-! # The exact transformed point and component under conjugacy -/

namespace DimensionFourDependence

open Matrix MvPolynomial

universe u
set_option maxHeartbeats 2800000
set_option synthInstance.maxHeartbeats 110000

variable {K : Type u} [Field K] {n : ℕ}

private theorem inverse_frame_embedded_point_relations
    (T S : Matrix (Fin n) (Fin n) K) (hTS : T * S = 1) (hST : S * T = 1)
    (H : Fin n → MvPolynomial (Fin n) K)
    (E G : Type u) [Field E] [Field G] [Algebra E G] [Algebra (polynomialOutputField H) E]
    [Algebra K E] [IsScalarTower K (polynomialOutputField H) E] [Algebra.IsAlgebraic (polynomialOutputField H) E]
    (f : FractionRing (MvPolynomial (Fin n) K) →+* G)
    (hcompat : ∀ a : polynomialOutputField H, f (a : FractionRing (MvPolynomial (Fin n) K)) =
      algebraMap E G (algebraMap (polynomialOutputField H) E a)) :
    letI := conjugateOutputAlgebra T S hTS hST H E
    let x := rationalCoordinate (K := K) (n := n)
    let y := S.map ((algebraMap E G).comp (algebraMap K E)) *ᵥ (f ∘ x)
    fiberVanishingIdeal (L := E) y ∈ (extendCoefficientIdeal E (fiberVanishingIdeal
      (L := polynomialOutputField (linearPolynomialConjugate T S H)) x)).minimalPrimes := by
  let M := polynomialOutputField H
  let M' := polynomialOutputField (linearPolynomialConjugate T S H)
  let F := FractionRing (MvPolynomial (Fin n) K)
  let x := rationalCoordinate (K := K) (n := n)
  let kG := (algebraMap E G).comp (algebraMap K E)
  have hK (c : K) : f (algebraMap K F c) = kG c := by
    change f ((algebraMap K M c : M) : F) = _
    rw [hcompat, ← IsScalarTower.algebraMap_apply K M E]
    rfl
  let : Algebra M' E := conjugateOutputAlgebra T S hTS hST H E
  let : Algebra.IsAlgebraic M' E := conjugateOutputAlgebra_isAlgebraic T S hTS hST H E
  let : Algebra M' G := ((algebraMap E G).comp (algebraMap M' E)).toAlgebra
  let : IsScalarTower M' E G := IsScalarTower.of_algebraMap_eq' rfl
  let g : F →ₐ[M'] G :=
    { toRingHom := f.comp (matrixSourceFractionEquiv T S hTS hST).symm.toRingHom
      commutes' := by
        intro a
        change f ((matrixSourceFractionEquiv T S hTS hST).symm (a : F)) = _
        rw [← conjugateOutputFieldEquiv_symm_source_value T S hTS hST H a]
        exact hcompat ((conjugateOutputFieldEquiv T S hTS hST H).symm a) }
  have hg : (g ∘ x : Fin n → G) = S.map kG *ᵥ (f ∘ x) := by
    funext i
    change f ((matrixSourceFractionEquiv T S hTS hST).symm (x i)) = _
    rw [matrixSourceFractionEquiv_symm_coordinate]
    simp only [map_sum, map_mul, Matrix.mulVec, dotProduct, Matrix.map_apply, Function.comp_apply]
    exact Finset.sum_congr rfl (fun j _ => congrArg (fun c => c * f (x j)) (hK (S i j)))
  change fiberVanishingIdeal (L := E) (S.map kG *ᵥ (f ∘ x)) ∈ _
  rw [← hg]
  exact embedded_source_relations_form_geometric_component g x

/-- The relations of the inverse linear coordinate change of a generic
component point form a genuine geometric component of the conjugate map. -/
theorem inverse_frame_point_relations_form_conjugate_component
    (T S : Matrix (Fin n) (Fin n) K) (hTS : T * S = 1) (hST : S * T = 1)
    (H : Fin n → MvPolynomial (Fin n) K)
    (E : Type u) [Field E] [Algebra (polynomialOutputField H) E] [Algebra K E]
    [IsScalarTower K (polynomialOutputField H) E] [Algebra.IsAlgebraic (polynomialOutputField H) E]
    (P : Ideal (MvPolynomial (Fin n) E)) [P.IsPrime]
    (hP : P ∈ (extendCoefficientIdeal E (fiberVanishingIdeal
      (L := polynomialOutputField H) (rationalCoordinate (K := K) (n := n)))).minimalPrimes) :
    letI := conjugateOutputAlgebra T S hTS hST H E
    let G := FractionRing (MvPolynomial (Fin n) E ⧸ P)
    let y := S.map ((algebraMap E G).comp (algebraMap K E)) *ᵥ primeQuotientCoordinate P
    fiberVanishingIdeal (L := E) y ∈ (extendCoefficientIdeal E (fiberVanishingIdeal
      (L := polynomialOutputField (linearPolynomialConjugate T S H))
      (rationalCoordinate (K := K) (n := n)))).minimalPrimes := by
  let M := polynomialOutputField H
  let G := FractionRing (MvPolynomial (Fin n) E ⧸ P)
  let x := rationalCoordinate (K := K) (n := n)
  obtain ⟨f, hf, hcompat⟩ := minimal_component_constructs_source_ringHom x
    (rationalSource_adjoin_coordinates_eq_top M) P hP
  have he := inverse_frame_embedded_point_relations T S hTS hST H E G f hcompat
  have hf' : (f ∘ x : Fin n → G) = primeQuotientCoordinate P := funext hf
  dsimp only at he ⊢
  rwa [hf'] at he

end DimensionFourDependence
