import DimensionFourDependence.CubicRadialBaseChange

/-! # Descending a cubic residue identity to its constant direction

The residue scalar in `Z+rY` need not be a constant. Radial shift
invariance over the residue field and injectivity of the coefficient
embedding nevertheless give the cubic equation over the original constants.
-/

namespace DimensionFourDependence

variable {E κ : Type*} [Field E] [Field κ] [Algebra E κ] {n : ℕ}

theorem matrixBilinearPairing_map (T : Matrix (Fin n) (Fin n) E) (x y : Fin n → E) :
    matrixBilinearPairing (T.map (algebraMap E κ))
      (fun i => algebraMap E κ (x i)) (fun i => algebraMap E κ (y i)) =
        algebraMap E κ (matrixBilinearPairing T x y) := by
  simp only [matrixBilinearPairing, Matrix.map_apply, map_sum, map_mul]

theorem tensorTrilinearPairing_map (C : Fin n → Fin n → Fin n → E) (x y z : Fin n → E) :
    tensorTrilinearPairing (fun i j k => algebraMap E κ (C i j k))
      (fun i => algebraMap E κ (x i)) (fun i => algebraMap E κ (y i))
      (fun i => algebraMap E κ (z i)) = algebraMap E κ (tensorTrilinearPairing C x y z) := by
  simp only [tensorTrilinearPairing, map_sum, map_mul]

/-- A cubic identity for a radially shifted residue direction implies
the constant direction's cubic identity in the original coefficient field. -/
theorem cubic_radial_residue_identity_descends
    (T : Matrix (Fin n) (Fin n) E) (C : Fin n → Fin n → Fin n → E)
    (h12 : ∀ i j k, C i j k = C j i k) (h23 : ∀ i j k, C i j k = C i k j)
    (Y Z : Fin n → E)
    (hY : ∀ j, (∑ i, Y i * T i j) = 0)
    (hCY : ∀ j k, (∑ i, Y i * C i j k) = -T j k)
    (hZ : matrixBilinearPairing T Z Z = 0) (r : κ)
    (hCubic : tensorTrilinearPairing (fun i j k => algebraMap E κ (C i j k))
      (fun i => algebraMap E κ (Z i) + r * algebraMap E κ (Y i))
      (fun i => algebraMap E κ (Z i) + r * algebraMap E κ (Y i))
      (fun i => algebraMap E κ (Z i) + r * algebraMap E κ (Y i)) = 0) :
    tensorTrilinearPairing C Z Z Z = 0 := by
  have hZm : matrixBilinearPairing (T.map (algebraMap E κ))
      (fun i => algebraMap E κ (Z i)) (fun i => algebraMap E κ (Z i)) = 0 := by
    rw [matrixBilinearPairing_map, hZ, map_zero]
  have hshift := symmetric_cubic_radial_shift (T.map (algebraMap E κ))
    (fun i j k => algebraMap E κ (C i j k))
    (fun i j k => congrArg (algebraMap E κ) (h12 i j k))
    (fun i j k => congrArg (algebraMap E κ) (h23 i j k))
    (fun i => algebraMap E κ (Y i)) (fun i => algebraMap E κ (Z i))
    (matrixBilinearPairing_radical_map T Y hY) (tensorTrilinearPairing_radial_map T C Y hCY) hZm r
  have hconstant := hshift.symm.trans hCubic
  rw [tensorTrilinearPairing_map] at hconstant
  exact (algebraMap E κ).injective (by simpa only [map_zero] using hconstant)

end DimensionFourDependence
