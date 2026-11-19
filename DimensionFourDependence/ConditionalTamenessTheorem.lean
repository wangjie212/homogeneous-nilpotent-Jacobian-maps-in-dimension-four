import DimensionFourDependence.DependentTernaryChartTameness
import DimensionFourDependence.TernaryClassificationSpecification

/-! # Assembly of Theorem 1.2 from the two remaining inputs in Section 6 -/

namespace DimensionFourDependence

open MvPolynomial

variable {K : Type*} [Field K] [CharZero K]
local notation "R₄" => MvPolynomial (Fin 4) K
local notation "Aut₄" => R₄ ≃ₐ[K] R₄

/-- Theorem 1.2 assembles from the cited ternary classification and the
constant-multiplier quadratic-pencil assertion. Only the degree-five
clause uses the quadratic-pencil assertion. -/
theorem original_homogeneous_tameness_of_ternary_classification
    (hclass : TernaryNilpotentClassification K)
    (d : ℕ) (hd : 0 < d) (H : Fin 4 → R₄) (hH : IsHomogMap H d)
    (hN : IsNilpotent (jac H)) :
    ∃ E : Aut₄, (∀ i, E (X i) = X i + H i) ∧ Shear.IsOneStablyTame E ∧
      (HasIndependentNormalizedTernaryChart H → E ∈ Tame.subgroup K 4) ∧
      (d ≤ 4 → E ∈ Tame.subgroup K 4) ∧
      (d ≤ 5 → Shear.QuadraticPencilShearsTame K → E ∈ Tame.subgroup K 4) := by
  classical
  by_cases hind : HasIndependentNormalizedTernaryChart H
  · obtain ⟨E, ht, hE⟩ :=
      original_tameness_of_independent_chart_of_ternary_classification hclass H hH hN hind
    exact ⟨E, hE, Shear.oneStablyTame_of_tame E ht, fun _ => ht, fun _ => ht, fun _ _ => ht⟩
  · obtain ⟨T, S, B, hTS, hST, hB, _, _⟩ :=
      original_homogeneous_nilpotent_map_constructs_fixed_coordinate_reduction H hd hH hN
    have hdep : ComponentsDependent (normalizedFixedCoordinateChart B) := by
      by_contra hn
      exact hind ⟨T, S, B, hTS, hST, hB, hn⟩
    obtain ⟨E, hE, hstable, ht4, ht5⟩ :=
      original_tameness_of_dependent_ternary_chart H hH hN T S hTS hST B hB hdep
    exact ⟨E, hE, hstable, fun hc => (hind hc).elim, ht4, ht5⟩

/-- The exact paper specification with the two outstanding statements
as explicit hypotheses. -/
theorem theorem_1_2_of_ternary_classification_and_quadratic_pencils
    (hclass : TernaryNilpotentClassification K) (hquadratic : Shear.QuadraticPencilShearsTame K) :
    TamenessTheorem K := by
  intro d hd H hH hN
  obtain ⟨E, hE, hs, hi, _, ht⟩ := original_homogeneous_tameness_of_ternary_classification
    hclass d hd H hH hN
  exact ⟨E, hE, hs, hi, fun h => ht h hquadratic⟩

end DimensionFourDependence
