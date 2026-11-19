import DimensionFourDependence.Proposition67

/-! # Corollary 6.10 over the original field -/

namespace DimensionFourDependence.Shear

variable {K : Type*} [Field K] [CharZero K]

theorem corollary_6_10 : QuadraticPencilShearsTame K :=
  quadratic_pencil_shears_tame_of_normalized Quintic.proposition_6_7

end DimensionFourDependence.Shear
