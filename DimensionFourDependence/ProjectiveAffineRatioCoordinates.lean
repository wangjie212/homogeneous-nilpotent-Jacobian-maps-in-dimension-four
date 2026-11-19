import DimensionFourDependence.Defs

/-! # The original three affine ratio coordinates in a specified projective frame -/

namespace DimensionFourDependence

variable {L : Type*} [Field L]

/-- The original affine ratios for the given original homogeneous
coordinates and original nonzero-frame index. -/
noncomputable def projectiveAffineRatioCoordinates
    (x : Fin 4 → L) (s : Fin 4 ≃ Option (Fin 3)) : Fin 3 → L :=
  fun i => x (s.symm (some i)) / x (s.symm none)

end DimensionFourDependence
