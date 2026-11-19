import DimensionFourDependence.ConjugateOutputConstants
import DimensionFourDependence.SourceRealizationFiberComponent

/-! # Actual geometric generic-fiber components under source-target conjugacy -/

namespace DimensionFourDependence

open Matrix MvPolynomial

set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {K : Type*} [Field K] {n : ℕ}

/-- A specified source-field realization transports to a genuine component
of the conjugated map, with its original constants and nonlinear curve. -/
theorem embedded_source_transport_under_linear_conjugacy
    (T S : Matrix (Fin n) (Fin n) K) (hTS : T * S = 1) (hST : S * T = 1)
    (H : Fin n → MvPolynomial (Fin n) K)
    (E G : Type*) [Field E] [Field G]
    [Algebra (polynomialOutputField H) E] [Algebra K E]
    [IsScalarTower K (polynomialOutputField H) E]
    [Algebra.IsAlgebraic (polynomialOutputField H) E]
    [Algebra E G] [Algebra K G] [IsScalarTower K E G]
    (Φ : FractionRing (MvPolynomial (Fin n) K) →+* G)
    (hcompat : ∀ a : polynomialOutputField H,
      Φ (a : FractionRing (MvPolynomial (Fin n) K)) =
        algebraMap E G (algebraMap (polynomialOutputField H) E a)) :
    letI := conjugateOutputAlgebra T S hTS hST H E
    ∃ (Q : Ideal (MvPolynomial (Fin n) E)) (_hQ : Q.IsPrime),
      Q ∈ (extendCoefficientIdeal E (fiberVanishingIdeal
        (L := polynomialOutputField (linearPolynomialConjugate T S H))
        (rationalCoordinate (K := K) (n := n)))).minimalPrimes ∧
      (LiesInAffineLine (E := E) (primeQuotientCoordinate Q) →
        LiesInAffineLine (E := E) (Φ ∘ rationalCoordinate (K := K) (n := n))) := by
  let M := polynomialOutputField H
  let M' := polynomialOutputField (linearPolynomialConjugate T S H)
  let F := FractionRing (MvPolynomial (Fin n) K)
  have hΦK (c : K) : Φ (algebraMap K F c) = algebraMap K G c := by
    change Φ ((algebraMap K M c : M) : F) = _
    rw [hcompat, ← IsScalarTower.algebraMap_apply K M E,
      ← IsScalarTower.algebraMap_apply K E G]
  let aM'E : Algebra M' E := conjugateOutputAlgebra T S hTS hST H E
  let tKM'E : IsScalarTower K M' E := conjugateOutputAlgebra_isScalarTower T S hTS hST H E
  let halg : Algebra.IsAlgebraic M' E := conjugateOutputAlgebra_isAlgebraic T S hTS hST H E
  let aM'G : Algebra M' G := ((algebraMap E G).comp (algebraMap M' E)).toAlgebra
  let tM'EG : IsScalarTower M' E G := IsScalarTower.of_algebraMap_eq' rfl
  let f' : F →ₐ[M'] G :=
    { toRingHom := Φ.comp (matrixSourceFractionEquiv T S hTS hST).symm.toRingHom
      commutes' := by
        intro a
        change Φ ((matrixSourceFractionEquiv T S hTS hST).symm (a : F)) = algebraMap M' G a
        rw [← conjugateOutputFieldEquiv_symm_source_value T S hTS hST H a, hcompat]
        rfl }
  let y : Fin n → G := f' ∘ rationalCoordinate (K := K) (n := n)
  have hy : y = S.map (algebraMap K G) *ᵥ (Φ ∘ rationalCoordinate (K := K) (n := n)) := by
    funext i
    change Φ ((matrixSourceFractionEquiv T S hTS hST).symm (rationalCoordinate (K := K) i)) = _
    rw [matrixSourceFractionEquiv_symm_coordinate]
    simp only [map_sum, map_mul, Matrix.mulVec, dotProduct, Matrix.map_apply,
      Function.comp_apply]
    exact Finset.sum_congr rfl (fun j _ =>
      congrArg (fun z => z * Φ (rationalCoordinate (K := K) j)) (hΦK (S i j)))
  let Q := fiberVanishingIdeal (L := E) y
  have hQ : Q.IsPrime := inferInstance
  have hminimal : Q ∈ (extendCoefficientIdeal E (fiberVanishingIdeal
      (L := M') (rationalCoordinate (K := K) (n := n)))).minimalPrimes :=
    embedded_source_relations_form_geometric_component f' (rationalCoordinate (K := K) (n := n))
  obtain ⟨g, hg⟩ := relation_prime_constructs_coordinate_embedding Q y rfl
  refine ⟨Q, hQ, hminimal, ?_⟩
  intro hline
  have hlineY := LiesInAffineLine.map_of_compatible g.toRingHom (RingHom.id E)
    (fun a => (g.commutes a).symm) (primeQuotientCoordinate Q) hline
  have hgy : g.toRingHom ∘ primeQuotientCoordinate Q = y := funext hg
  rw [hgy, hy] at hlineY
  have hmapE : S.map (algebraMap K E) * T.map (algebraMap K E) = 1 := by
    rw [← Matrix.map_mul, hST]
    ext i j
    simp [Matrix.one_apply]
  have hback := hlineY.mulVec (T.map (algebraMap K E)) (S.map (algebraMap K E)) hmapE
  have hcoeff : (T.map (algebraMap K E)).map (algebraMap E G) = T.map (algebraMap K G) := by
    ext i j
    exact (IsScalarTower.algebraMap_apply K E G (T i j)).symm
  have hmapG : T.map (algebraMap K G) * S.map (algebraMap K G) = 1 := by
    rw [← Matrix.map_mul, hTS]
    ext i j
    simp [Matrix.one_apply]
  simpa only [hcoeff, Matrix.mulVec_mulVec, hmapG, Matrix.one_mulVec] using hback

/-- A specified original geometric component transports to an actual
component of the conjugated map over the same constants. A line on the
transported component would give a line on the original component. -/
theorem geometric_component_transport_under_linear_conjugacy
    (T S : Matrix (Fin n) (Fin n) K) (hTS : T * S = 1) (hST : S * T = 1)
    (H : Fin n → MvPolynomial (Fin n) K)
    (E : Type*) [Field E] [Algebra (polynomialOutputField H) E] [Algebra K E]
    [IsScalarTower K (polynomialOutputField H) E]
    [Algebra.IsAlgebraic (polynomialOutputField H) E]
    (P : Ideal (MvPolynomial (Fin n) E)) [P.IsPrime]
    (hP : P ∈ (extendCoefficientIdeal E (fiberVanishingIdeal
      (L := polynomialOutputField H) (rationalCoordinate (K := K) (n := n)))).minimalPrimes) :
    letI := conjugateOutputAlgebra T S hTS hST H E
    ∃ (Q : Ideal (MvPolynomial (Fin n) E)) (_hQ : Q.IsPrime),
      Q ∈ (extendCoefficientIdeal E (fiberVanishingIdeal
        (L := polynomialOutputField (linearPolynomialConjugate T S H))
        (rationalCoordinate (K := K) (n := n)))).minimalPrimes ∧
      (LiesInAffineLine (E := E) (primeQuotientCoordinate Q) →
        LiesInAffineLine (E := E) (primeQuotientCoordinate P)) := by
  obtain ⟨Φ, hΦ, hcompat⟩ := minimal_component_constructs_source_ringHom
    (rationalCoordinate (K := K) (n := n))
    (rationalSource_adjoin_coordinates_eq_top (polynomialOutputField H)) P hP
  have htransport := embedded_source_transport_under_linear_conjugacy
    T S hTS hST H E (FractionRing (MvPolynomial (Fin n) E ⧸ P)) Φ hcompat
  let aM'E := conjugateOutputAlgebra T S hTS hST H E
  obtain ⟨Q, hQ, hminimal, hback⟩ := htransport
  refine ⟨Q, hQ, hminimal, ?_⟩
  intro hline
  have he := hback hline
  have hcoords : Φ ∘ rationalCoordinate (K := K) (n := n) = primeQuotientCoordinate P := funext hΦ
  rwa [hcoords] at he

end DimensionFourDependence
