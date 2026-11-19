import DimensionFourDependence.LinePairIncidenceMatrix
import DimensionFourDependence.MatrixKernelDescent

/-! # The intersection point of two actual distinct lines descends

The incidence matrix has a one-dimensional kernel when its two lines
are distinct and intersect. Its rank is unchanged by field extension.
The checked kernel-descent theorem therefore expresses every nonzero
extended intersection vector as a scalar multiple of a vector defined
over the matrix-parameter field.
-/

namespace DimensionFourDependence

open Matrix Module

variable {F E : Type*} [Field F] [Field E] [Algebra F E]

/-- Two distinct actual lines with a common nonzero point have a
rank-three actual incidence matrix. -/
theorem distinct_intersecting_chart_lines_incidence_rank_three
    (p q : Equiv.Perm (Fin 4)) (B D : Matrix (Fin 2) (Fin 2) F)
    (O : Fin 4 → F) (hO : O ≠ 0)
    (hB : O ∈ lineChartMemberLine p B) (hD : O ∈ lineChartMemberLine q D)
    (hne : lineChartMemberLine p B ≠ lineChartMemberLine q D) :
    (linePairIncidenceMatrix p q B D).rank = 3 := by
  have hmeet : lineChartMemberLine p B ⊓ lineChartMemberLine q D ≠ ⊥ := by
    intro hz
    have hmem : O ∈ lineChartMemberLine p B ⊓ lineChartMemberLine q D := ⟨hB, hD⟩
    rw [hz, Submodule.mem_bot] at hmem
    exact hO hmem
  have hinf := (distinct_intersecting_lines_dimensions _ _
    (lineChartMemberLine_finrank p B) (lineChartMemberLine_finrank q D) hne hmeet).1
  have hk : finrank F (LinearMap.ker (linePairIncidenceMatrix p q B D).toLin') = 1 := by
    rw [linePairIncidenceMatrix_ker]
    exact hinf
  have hd := LinearMap.finrank_range_add_finrank_ker (linePairIncidenceMatrix p q B D).toLin'
  simp only [Module.finrank_pi, Fintype.card_fin] at hd
  change (linePairIncidenceMatrix p q B D).rank +
    finrank F (LinearMap.ker (linePairIncidenceMatrix p q B D).toLin') = 4 at hd
  omega

/-- The projective intersection point of two distinct actual lines is
defined over their original matrix-parameter field, even when the given
intersection vector is over a larger field. -/
theorem distinct_chart_line_intersection_point_descends
    (p q : Equiv.Perm (Fin 4)) (B D : Matrix (Fin 2) (Fin 2) F)
    (O : Fin 4 → E) (hO : O ≠ 0)
    (hB : O ∈ lineChartMemberLine p (B.map (algebraMap F E)))
    (hD : O ∈ lineChartMemberLine q (D.map (algebraMap F E)))
    (hne : lineChartMemberLine p (B.map (algebraMap F E)) ≠
      lineChartMemberLine q (D.map (algebraMap F E))) :
    ∃ v : Fin 4 → F, v ≠ 0 ∧
      v ∈ lineChartMemberLine p B ∧ v ∈ lineChartMemberLine q D ∧
      ∃ t : E, t ≠ 0 ∧ O = t • (fun i => algebraMap F E (v i)) := by
  have hrE := distinct_intersecting_chart_lines_incidence_rank_three p q
    (B.map (algebraMap F E)) (D.map (algebraMap F E)) O hO hB hD hne
  have hr : (linePairIncidenceMatrix p q B D).rank = 3 := by
    rw [← matrix_rank_field_map (algebraMap F E) (linePairIncidenceMatrix p q B D),
      linePairIncidenceMatrix_map]
    exact hrE
  have hAO : (linePairIncidenceMatrix p q B D).map (algebraMap F E) *ᵥ O = 0 := by
    rw [linePairIncidenceMatrix_map]
    exact (linePairIncidenceMatrix_mulVec_zero_iff p q _ _ O).mpr ⟨hB, hD⟩
  obtain ⟨v, hv, hAv, t, ht, he⟩ := rank_three_kernel_vector_after_extension
    (linePairIncidenceMatrix p q B D) hr O hO hAO
  have hm := (linePairIncidenceMatrix_mulVec_zero_iff p q B D v).mp hAv
  exact ⟨v, hv, hm.1, hm.2, t, ht, he⟩

end DimensionFourDependence
