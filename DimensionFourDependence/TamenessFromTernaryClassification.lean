import DimensionFourDependence.ConditionalTamenessTheorem
import DimensionFourDependence.Corollary610

/-! # The proof of Theorem 1.2 reduced to its cited classification -/

namespace DimensionFourDependence

variable {K : Type*} [Field K] [CharZero K]

theorem theorem_1_2_of_ternary_classification
    (hclass : TernaryNilpotentClassification K) : TamenessTheorem K :=
  theorem_1_2_of_ternary_classification_and_quadratic_pencils hclass Shear.corollary_6_10

end DimensionFourDependence
