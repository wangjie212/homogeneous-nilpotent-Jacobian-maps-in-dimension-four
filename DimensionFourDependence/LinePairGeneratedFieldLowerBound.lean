import DimensionFourDependence.LinePairIntersectionDescent
import DimensionFourDependence.GeneratedFieldDimension
import DimensionFourDependence.OutputCoordinateFieldEquiv

/-! # The actual generic intersecting-line pair has dimension at least two

The projective intersection point descends to the pair's generated
parameter field. Its output field is contained in that field with one
extra scalar adjoined, so its dimension is at most the pair dimension
plus one. The actual generic image output field has dimension three.
Consequently the actual distinct pair has dimension at least two.
-/

namespace DimensionFourDependence

open MvPolynomial Matrix

universe u

variable {K E : Type u} [Field K] [Field E] [Algebra K E]

/-- A point which is a scalar multiple of a vector over an actual
intermediate parameter field adds at most one to its dimension. -/
theorem outputField_trdeg_le_parameter_add_one
    (F : IntermediateField K E) (O : Fin 4 → E) (v : Fin 4 → F) (t : E)
    (he : O = t • (fun i => algebraMap F E (v i))) :
    Algebra.trdeg K (fullOutputField (K := K) O) ≤ Algebra.trdeg K F + 1 := by
  let J := IntermediateField.adjoin K ((F : Set E) ∪ {t})
  have hO : fullOutputField (K := K) O ≤ J := by
    apply IntermediateField.adjoin_le_iff.mpr
    rintro _ ⟨i, rfl⟩
    rw [he]
    change t * (v i : E) ∈ J
    exact J.mul_mem (IntermediateField.subset_adjoin K _ (Or.inr rfl))
      (IntermediateField.subset_adjoin K _ (Or.inl (v i).property))
  have hinc := trdeg_le_of_injective (IntermediateField.inclusion hO)
    (IntermediateField.inclusion hO).injective
  have hgen := generatedField_union_trdeg_le_sum (K := K) (F : Set E) {t}
  rw [IntermediateField.adjoin_self] at hgen
  exact hinc.trans (hgen.trans (add_le_add le_rfl (generatedField_singleton_trdeg_le_one (K := K) t)))

/-- Two distinct actual lines through a point with output-field
dimension three have joint parameter-field dimension at least two. -/
theorem distinct_line_pair_generated_field_trdeg_ge_two
    (p q : Equiv.Perm (Fin 4)) (B D : Matrix (Fin 2) (Fin 2) E)
    (O : Fin 4 → E) (hO : O ≠ 0)
    (hB : O ∈ lineChartMemberLine p B) (hD : O ∈ lineChartMemberLine q D)
    (hne : lineChartMemberLine p B ≠ lineChartMemberLine q D)
    (hOdim : Algebra.trdeg K (fullOutputField (K := K) O) = 3) :
    2 ≤ Algebra.trdeg K (IntermediateField.adjoin K (Set.range (linePairCoordinates B D))) := by
  let F := IntermediateField.adjoin K (Set.range (linePairCoordinates B D))
  let BF : Matrix (Fin 2) (Fin 2) F := fun i j =>
    ⟨B i j, IntermediateField.subset_adjoin K _ ⟨Sum.inl (i, j), rfl⟩⟩
  let DF : Matrix (Fin 2) (Fin 2) F := fun i j =>
    ⟨D i j, IntermediateField.subset_adjoin K _ ⟨Sum.inr (i, j), rfl⟩⟩
  have hBF : BF.map (algebraMap F E) = B := rfl
  have hDF : DF.map (algebraMap F E) = D := rfl
  obtain ⟨v, _, _, _, t, _, he⟩ := distinct_chart_line_intersection_point_descends p q BF DF O hO
    (by rw [hBF]; exact hB) (by rw [hDF]; exact hD) (by rw [hBF, hDF]; exact hne)
  have hbound := outputField_trdeg_le_parameter_add_one (K := K) F O v t he
  rw [hOdim] at hbound
  change 2 ≤ Algebra.trdeg K F
  by_contra hn
  have hlt : Algebra.trdeg K F < 2 := lt_of_not_ge hn
  obtain ⟨n, heq⟩ := Cardinal.lt_aleph0.mp (hlt.trans (by simp))
  rw [heq] at hlt hbound
  have hnlt : n < 2 := by exact_mod_cast hlt
  have hnlo : 3 ≤ n + 1 := by exact_mod_cast hbound
  omega

variable [CharZero K]

/-- The actual generic image point has output-field dimension three,
using precisely its actual original polynomial relations. -/
theorem genericOutputValue_output_field_trdeg_three
    (H : Fin 4 → MvPolynomial (Fin 4) K) (hrank : polyRank (jac H) = 3)
    [Algebra (polynomialOutputField H) E] [IsScalarTower K (polynomialOutputField H) E] :
    Algebra.trdeg K (fullOutputField (K := K) (genericOutputValue H E)) = 3 := by
  have hrel : fiberVanishingIdeal (L := K) (genericOutputValue H E) =
      fiberVanishingIdeal (L := K) (fun i => algebraMap (MvPolynomial (Fin 4) K)
        (FractionRing (MvPolynomial (Fin 4) K)) (H i)) := by
    rw [← imageRelationIdeal_eq_rational_relations]
    ext P
    exact genericOutputValue_relations H E P
  have he := (outputFieldEquivOfRelations (genericOutputValue H E)
    (fun i => algebraMap (MvPolynomial (Fin 4) K)
      (FractionRing (MvPolynomial (Fin 4) K)) (H i)) hrel).trdeg_eq
  exact he.trans ((polynomialOutputField_trdeg_eq_rank H).trans (by rw [hrank]; norm_num))

/-- The actual distinct pair through the actual generic image value
has joint parameter-field dimension at least two, with no dimension
or incidence-density hypothesis. -/
theorem actual_generic_distinct_line_pair_trdeg_ge_two
    (H : Fin 4 → MvPolynomial (Fin 4) K) (hrank : polyRank (jac H) = 3)
    [Algebra (polynomialOutputField H) E] [IsScalarTower K (polynomialOutputField H) E]
    (p q : Equiv.Perm (Fin 4)) (B D : Matrix (Fin 2) (Fin 2) E)
    (hB : genericOutputValue H E ∈ lineChartMemberLine p B)
    (hD : genericOutputValue H E ∈ lineChartMemberLine q D)
    (hne : lineChartMemberLine p B ≠ lineChartMemberLine q D) :
    2 ≤ Algebra.trdeg K (IntermediateField.adjoin K (Set.range (linePairCoordinates B D))) := by
  exact distinct_line_pair_generated_field_trdeg_ge_two p q B D (genericOutputValue H E)
    (genericOutputValue_ne_zero H (rank_three_polynomial_map_ne_zero H hrank) E) hB hD hne
    (genericOutputValue_output_field_trdeg_three H hrank)

end DimensionFourDependence
