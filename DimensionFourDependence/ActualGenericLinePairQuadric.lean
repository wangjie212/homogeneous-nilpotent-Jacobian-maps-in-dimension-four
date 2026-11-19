import DimensionFourDependence.TwoDimensionalLinePairQuadric
import DimensionFourDependence.LinePairGeneratedFieldLowerBound

/-! # Actual generic distinct image lines force the actual smooth quadric

The actual pair's dimension lower bound is now derived from its common
generic image point. The actual component product has dimension at most
two, so the pair has exactly its product relations. Its incidence equation
therefore holds on all member pairs, and the checked skew-triple and
covering-density argument gives the actual determinant quadric.
-/

namespace DimensionFourDependence

open MvPolynomial Matrix

universe u

variable {K E : Type u} [Field K] [CharZero K] [IsAlgClosed K] [Field E] [Algebra K E]

/-- The actual distinct generic pair has precisely the relations of
the product of its original covering-curve components. This supplies
the required incidence-density comparison without a dimension assumption
on the actual pair. -/
theorem actual_generic_distinct_pair_relations_eq_product
    (H : Fin 4 → MvPolynomial (Fin 4) K) (hrank : polyRank (jac H) = 3)
    [Algebra (polynomialOutputField H) E] [IsScalarTower K (polynomialOutputField H) E]
    (Q Q' : Ideal (MvPolynomial LineMatrixIndex K)) [Q.IsPrime] [Q'.IsPrime]
    (hQ : Algebra.trdeg K (FractionRing (MvPolynomial LineMatrixIndex K ⧸ Q)) = 1)
    (hQ' : Algebra.trdeg K (FractionRing (MvPolynomial LineMatrixIndex K ⧸ Q')) = 1)
    (p q : Equiv.Perm (Fin 4)) (B D : Matrix (Fin 2) (Fin 2) E)
    (hB : Q ≤ (extendedLineChartPrime (K := K) B).asIdeal)
    (hD : Q' ≤ (extendedLineChartPrime (K := K) D).asIdeal)
    (hOB : genericOutputValue H E ∈ lineChartMemberLine p B)
    (hOD : genericOutputValue H E ∈ lineChartMemberLine q D)
    (hne : lineChartMemberLine p B ≠ lineChartMemberLine q D) :
    RingHom.ker (aeval (linePairCoordinates B D) : MvPolynomial LinePairIndex K →ₐ[K] E) =
      lineComponentPairIdeal Q Q' := by
  exact line_pair_relations_eq_product_of_dimension_two Q Q' hQ hQ' B D hB hD
    (actual_generic_distinct_line_pair_trdeg_ge_two H hrank p q B D hOB hOD hne)

/-- Every original-field pair of members of the two actual covering
curve components is incident, derived from the actual distinct generic pair. -/
theorem actual_generic_distinct_pair_forces_component_incidence
    (H : Fin 4 → MvPolynomial (Fin 4) K) (hrank : polyRank (jac H) = 3)
    [Algebra (polynomialOutputField H) E] [IsScalarTower K (polynomialOutputField H) E]
    (Q Q' : Ideal (MvPolynomial LineMatrixIndex K)) [Q.IsPrime] [Q'.IsPrime]
    (hQ : Algebra.trdeg K (FractionRing (MvPolynomial LineMatrixIndex K ⧸ Q)) = 1)
    (hQ' : Algebra.trdeg K (FractionRing (MvPolynomial LineMatrixIndex K ⧸ Q')) = 1)
    (p q : Equiv.Perm (Fin 4)) (B D : Matrix (Fin 2) (Fin 2) E)
    (hB : Q ≤ (extendedLineChartPrime (K := K) B).asIdeal)
    (hD : Q' ≤ (extendedLineChartPrime (K := K) D).asIdeal)
    (hOB : genericOutputValue H E ∈ lineChartMemberLine p B)
    (hOD : genericOutputValue H E ∈ lineChartMemberLine q D)
    (hne : lineChartMemberLine p B ≠ lineChartMemberLine q D) :
    ∀ C : lineComponentPoints Q, ∀ T : lineComponentPoints Q',
      ¬ Disjoint (lineChartMemberLine p C.val) (lineChartMemberLine q T.val) := by
  have hmeet : ¬ Disjoint (lineChartMemberLine p B) (lineChartMemberLine q D) := by
    intro h
    exact genericOutputValue_ne_zero H (rank_three_polynomial_map_ne_zero H hrank) E
      (Submodule.disjoint_def.mp h (genericOutputValue H E) hOB hOD)
  exact two_dimensional_incident_pair_forces_component_incidence Q Q' hQ hQ' p q B D hB hD
    (actual_generic_distinct_line_pair_trdeg_ge_two H hrank p q B D hOB hOD hne) hmeet

/-- Two actual distinct lines through the actual generic image point
identify the original Gauss-dimension-two image with the determinant
quadric. All covering, dimension and incidence obligations are derived. -/
theorem actual_generic_distinct_image_lines_force_quadric
    (H : Fin 4 → MvPolynomial (Fin 4) K) {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d)
    (hN : IsNilpotent (jac H)) (hrank : polyRank (jac H) = 3)
    (hind : ¬ ComponentsDependent H) (I : ImageRelationWitness H)
    (hGauss : gaussImageDimension H I = 2)
    [Algebra (polynomialOutputField H) E] [IsScalarTower K (polynomialOutputField H) E]
    (s t : hypersurfaceLineAtlas (MvPolynomial.map (algebraMap K E) I.equation))
    (hs : genericOutputValue H E ∈ hypersurfaceAtlasLine _ s)
    (ht : genericOutputValue H E ∈ hypersurfaceAtlasLine _ t)
    (hne : hypersurfaceAtlasLine _ s ≠ hypersurfaceAtlasLine _ t) :
    I.degree = 2 ∧
      ∃ e : (Fin 4 → K) ≃ₗ[K] ((Fin 2 → K) × (Fin 2 → K)),
        ∀ x : Fin 4 → K, aeval x I.equation = 0 ↔ standardRulingQuadric (e x) = 0 := by
  apply actual_generic_line_pair_quadric_of_pair_dimension_two H hd hH hN hrank hind I hGauss s t hs ht
  exact actual_generic_distinct_line_pair_trdeg_ge_two H hrank s.1 t.1 s.2.val t.2.val hs ht hne

end DimensionFourDependence
