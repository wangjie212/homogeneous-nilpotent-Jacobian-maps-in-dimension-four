import DimensionFourDependence.OriginalFieldRankTwoNilpotentDependence
import DimensionFourDependence.OriginalFieldTernaryDependence
import DimensionFourDependence.OriginalRankThreeTernaryReduction

/-! # Theorem 1.1: homogeneous nilpotent-Jacobian maps in dimension four have a constant component relation -/

namespace DimensionFourDependence

open Matrix MvPolynomial

universe u
set_option maxHeartbeats 4000000

variable {K : Type u} [Field K] [CharZero K]
local notation "R₀" => MvPolynomial (Fin 4) K

section ClosedConstants

variable [IsAlgClosed K]

/-- The complete original rank-three branch, with the homogeneous
ternary theorem proved rather than supplied as an additional input. -/
theorem closed_field_positive_homogeneous_rank_three_nilpotent_componentsDependent
    (H : Fin 4 → R₀) {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d)
    (hN : IsNilpotent (jac H)) (hrank : polyRank (jac H) = 3) : ComponentsDependent H :=
  original_rank_three_dependence_of_homogeneous_ternary_dependence
    (fun _ hd G hG hnil => closed_field_positive_homogeneous_ternary_nilpotent_componentsDependent G hd hG hnil)
    H hd hH hN hrank

/-- All possible nilpotent ranks are discharged over the original
closed characteristic-zero constants, in every positive degree. -/
theorem closed_field_positive_homogeneous_four_variable_nilpotent_componentsDependent
    (H : Fin 4 → R₀) {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d)
    (hN : IsNilpotent (jac H)) : ComponentsDependent H := by
  have hr := rank_at_most_three H hN
  by_cases hr3 : polyRank (jac H) = 3
  · exact closed_field_positive_homogeneous_rank_three_nilpotent_componentsDependent H hd hH hN hr3
  · exact original_field_positive_homogeneous_rank_at_most_two_nilpotent_componentsDependent H hd hH hN (by omega)

end ClosedConstants

/-- **Theorem 1.1** of `dimension_four_dependence.pdf`, over every
original characteristic-zero coefficient field and in every positive
homogeneous degree. The full original constant component relation is
proved; no lower-dimensional dependence or geometric classification
is assumed. -/
theorem theorem_1_1 : DependenceTheorem K := by
  intro d hd H hH hN
  apply componentsDependent_of_map (AlgebraicClosure K) H
  exact closed_field_positive_homogeneous_four_variable_nilpotent_componentsDependent
    (fun i => MvPolynomial.map (algebraMap K (AlgebraicClosure K)) (H i)) hd
    (isHomogMap_map_coefficients H hH) (nilpotent_jac_map_coefficients H hN)

/-- The explicit original-field constant coefficient relation in
the paper's polynomial form of Theorem 1.1. -/
theorem theorem_1_1_original_constant_linear_relation
    (H : Fin 4 → R₀) {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d)
    (hN : IsNilpotent (jac H)) :
    ∃ c : Fin 4 → K, c ≠ 0 ∧ ∑ i, C (c i) * H i = 0 := by
  obtain ⟨c, hc, hrel⟩ := theorem_1_1 d hd H hH hN
  exact ⟨c, hc, by simpa only [MvPolynomial.smul_eq_C_mul] using hrel⟩

/-- The conclusion of Proposition 2.1 over the original field. The
proved rank-three statement is stronger than the proposition's
additional affine-line-fiber hypothesis. -/
theorem proposition_2_1
    (H : Fin 4 → R₀) {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d)
    (hN : IsNilpotent (jac H)) (_hrank : polyRank (jac H) = 3) : ComponentsDependent H :=
  theorem_1_1 d hd H hH hN

end DimensionFourDependence
