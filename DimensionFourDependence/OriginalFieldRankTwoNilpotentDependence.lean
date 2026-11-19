import DimensionFourDependence.HomogeneousRankTwoNilpotentDependence
import DimensionFourDependence.ScalarExtendedMapHypotheses
import DimensionFourDependence.SmallerSourceDependenceTransport

/-! # The entire rank-at-most-two dependence branch over arbitrary original constants -/

namespace DimensionFourDependence

open Matrix MvPolynomial

universe u
set_option maxHeartbeats 3000000

variable {K : Type u} [Field K] [CharZero K]
local notation "R₀" => MvPolynomial (Fin 4) K

/-- The full general-degree rank-two nilpotent dependence theorem
over every original characteristic-zero field. Actual coefficient
extension preserves homogeneity, nilpotence and source Jacobian rank;
the closed-field component relation descends to original constants. -/
theorem original_field_positive_homogeneous_rank_two_nilpotent_componentsDependent
    (H : Fin 4 → R₀) {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d)
    (hN : IsNilpotent (jac H)) (hrank : polyRank (jac H) = 2) :
    ComponentsDependent H := by
  apply componentsDependent_of_map (AlgebraicClosure K) H
  exact closed_field_positive_homogeneous_rank_two_nilpotent_componentsDependent
    (fun i => MvPolynomial.map (algebraMap K (AlgebraicClosure K)) (H i)) hd
    (isHomogMap_map_coefficients H hH) (nilpotent_jac_map_coefficients H hN)
    ((polyRank_jac_map_coefficients H).trans hrank)

/-- Every positive homogeneous four-variable map with nilpotent
Jacobian of rank at most two has dependent components over its
original characteristic-zero field, in arbitrary degree. This closes
the entire lower-rank branch of Theorem 1.1. -/
theorem original_field_positive_homogeneous_rank_at_most_two_nilpotent_componentsDependent
    (H : Fin 4 → R₀) {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d)
    (hN : IsNilpotent (jac H)) (hrank : polyRank (jac H) ≤ 2) :
    ComponentsDependent H := by
  by_cases hr2 : polyRank (jac H) = 2
  · exact original_field_positive_homogeneous_rank_two_nilpotent_componentsDependent H hd hH hN hr2
  · exact positive_homogeneous_rank_at_most_one_componentsDependent (by norm_num) H hd hH (by omega)

end DimensionFourDependence
