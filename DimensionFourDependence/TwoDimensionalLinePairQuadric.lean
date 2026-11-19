import DimensionFourDependence.LinePairDimensionDensity
import DimensionFourDependence.LinePairIncidenceMatrix
import DimensionFourDependence.CoveringTransversalQuadric

/-! # From an actual two-dimensional intersecting pair to the actual image quadric

The actual incidence determinant vanishes on the extension-field pair.
The dimension comparison makes that pair generic in the original
component product, so the determinant vanishes on every actual member
pair. The checked covering-family argument then identifies the original
image equation with a determinant quadric. The lower bound on the actual
pair's generated field is the remaining input to this reduction.
-/

namespace DimensionFourDependence

open MvPolynomial Matrix

universe u

variable {K E : Type u} [Field K] [IsAlgClosed K] [Field E] [Algebra K E]
variable (Q Q' : Ideal (MvPolynomial LineMatrixIndex K)) [Q.IsPrime] [Q'.IsPrime]

/-- One two-dimensional intersecting extension-field pair forces actual
incidence of every original-field pair in its two covering components. -/
theorem two_dimensional_incident_pair_forces_component_incidence
    (hQ : Algebra.trdeg K (FractionRing (MvPolynomial LineMatrixIndex K ⧸ Q)) = 1)
    (hQ' : Algebra.trdeg K (FractionRing (MvPolynomial LineMatrixIndex K ⧸ Q')) = 1)
    (p q : Equiv.Perm (Fin 4)) (B D : Matrix (Fin 2) (Fin 2) E)
    (hB : Q ≤ (extendedLineChartPrime (K := K) B).asIdeal)
    (hD : Q' ≤ (extendedLineChartPrime (K := K) D).asIdeal)
    (hdim : 2 ≤ Algebra.trdeg K (IntermediateField.adjoin K (Set.range (linePairCoordinates B D))))
    (hmeet : ¬ Disjoint (lineChartMemberLine p B) (lineChartMemberLine q D)) :
    ∀ C : lineComponentPoints Q, ∀ T : lineComponentPoints Q',
      ¬ Disjoint (lineChartMemberLine p C.val) (lineChartMemberLine q T.val) := by
  intro C T
  apply (linePairIncidencePolynomial_zero_iff (K := K) p q C.val T.val).mp
  exact line_pair_equation_holds_on_product_of_dimension_two Q Q' hQ hQ' B D hB hD hdim
    (linePairIncidencePolynomial p q)
    ((linePairIncidencePolynomial_zero_iff (K := K) p q B D).mpr hmeet) C.val C.property T.val T.property

variable [CharZero K]

omit [Q.IsPrime] [Q'.IsPrime] in
/-- The original Gauss-dimension-two image is the determinant quadric
as soon as its actual generic image-line pair has generated field
dimension at least two. Covering components, their dimensions, incidence
and the actual skew triple are all derived in this reduction. -/
theorem actual_generic_line_pair_quadric_of_pair_dimension_two
    (H : Fin 4 → MvPolynomial (Fin 4) K) {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d)
    (hN : IsNilpotent (jac H)) (hrank : polyRank (jac H) = 3)
    (hind : ¬ ComponentsDependent H) (I : ImageRelationWitness H)
    (hGauss : gaussImageDimension H I = 2)
    [Algebra (polynomialOutputField H) E] [IsScalarTower K (polynomialOutputField H) E]
    (s t : hypersurfaceLineAtlas (MvPolynomial.map (algebraMap K E) I.equation))
    (hs : genericOutputValue H E ∈ hypersurfaceAtlasLine _ s)
    (ht : genericOutputValue H E ∈ hypersurfaceAtlasLine _ t)
    (hdim : 2 ≤ Algebra.trdeg K (IntermediateField.adjoin K
      (Set.range (linePairCoordinates s.2.val t.2.val)))) :
    I.degree = 2 ∧
      ∃ e : (Fin 4 → K) ≃ₗ[K] ((Fin 2 → K) × (Fin 2 → K)),
        ∀ x : Fin 4 → K, aeval x I.equation = 0 ↔ standardRulingQuadric (e x) = 0 := by
  obtain ⟨Q, hQ, hB, hk, _, hQdim⟩ :=
    generic_image_line_exists_one_dimensional_covering_component H hd hH hrank hind I s hs
  obtain ⟨Q', hQ', hD, hk', _, hQ'dim⟩ :=
    generic_image_line_exists_one_dimensional_covering_component H hd hH hrank hind I t ht
  let : Q.IsPrime := hQ.isPrime
  let : Q'.IsPrime := hQ'.isPrime
  have hmeet : ¬ Disjoint (lineChartMemberLine s.1 s.2.val) (lineChartMemberLine t.1 t.2.val) := by
    intro h
    exact genericOutputValue_ne_zero H (rank_three_polynomial_map_ne_zero H hrank) E
      (Submodule.disjoint_def.mp h (genericOutputValue H E) hs ht)
  apply pairwise_incident_covering_components_identify_image_quadric Q H hd hH hN hrank hind I hGauss
    s.1 hQ.le hk Q' t.1 hk'
  exact two_dimensional_incident_pair_forces_component_incidence Q Q' hQdim hQ'dim
    s.1 t.1 s.2.val t.2.val hB hD hdim hmeet

end DimensionFourDependence
