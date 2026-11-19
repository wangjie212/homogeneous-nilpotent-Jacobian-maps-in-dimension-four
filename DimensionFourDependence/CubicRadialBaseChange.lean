import DimensionFourDependence.CubicRadialShift

/-! # Radial cubic shift invariance over residue and extension fields -/

namespace DimensionFourDependence

variable {F G : Type*} [Field F] [Field G] [Algebra F G] {n : ℕ}

/-- The radial cubic contraction identity persists after any field extension. -/
theorem tensorTrilinearPairing_radial_map
    (T : Matrix (Fin n) (Fin n) F) (C : Fin n → Fin n → Fin n → F) (Y : Fin n → F)
    (hC : ∀ j k, (∑ i, Y i * C i j k) = -T j k) (v w : Fin n → G) :
    tensorTrilinearPairing (fun i j k => algebraMap F G (C i j k))
      (fun i => algebraMap F G (Y i)) v w = -matrixBilinearPairing (T.map (algebraMap F G)) v w := by
  unfold tensorTrilinearPairing matrixBilinearPairing
  rw [Finset.sum_comm, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.sum_comm, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro k _
  rw [← Finset.sum_mul, ← Finset.sum_mul]
  have he : (∑ i, algebraMap F G (C i j k) * algebraMap F G (Y i)) =
      -algebraMap F G (T j k) := by
    simp only [← map_mul, ← map_sum]
    have hb : (∑ i, C i j k * Y i) = -T j k := by
      simpa only [mul_comm] using hC j k
    rw [hb, map_neg]
  change (∑ i, algebraMap F G (C i j k) * algebraMap F G (Y i)) * v j * w k =
    -(algebraMap F G (T j k) * v j * w k)
  rw [he]
  ring

variable {K : Type*} [Field K] [CharZero K]

/-- The actual coefficient cubic has the same self-value on `Z+rY`
as on `Z`, over every further field, when `Z` is Hessian-isotropic. -/
theorem coefficientCubicTensor_radial_shift_over
    (Y : Fin 3 → FractionRing (MvPolynomial (Fin 4) K)) (hY : AlgebraicIndependent K Y)
    (h : coefficientField (K := K) Y) (hh : coefficientEuler Y hY h = h)
    (A : Type*) [Field A] [Algebra (coefficientField (K := K) Y) A]
    (Z : Fin 3 → A)
    (hZ : matrixBilinearPairing ((coefficientHessian Y hY h).map
      (algebraMap (coefficientField (K := K) Y) A)) Z Z = 0) (r : A) :
    let L := coefficientField (K := K) Y
    let C := fun i j k => algebraMap L A (coefficientCubicTensor Y hY h i j k)
    let y := fun i => algebraMap L A (coefficientCoordinate (K := K) Y i)
    tensorTrilinearPairing C (fun i => Z i + r * y i) (fun i => Z i + r * y i)
      (fun i => Z i + r * y i) = tensorTrilinearPairing C Z Z Z := by
  let L := coefficientField (K := K) Y
  let T := (coefficientHessian Y hY h).map (algebraMap L A)
  let C := fun i j k => algebraMap L A (coefficientCubicTensor Y hY h i j k)
  let y := fun i => algebraMap L A (coefficientCoordinate (K := K) Y i)
  apply symmetric_cubic_radial_shift T C
    (fun i j k => congrArg (algebraMap L A) (coefficientCubicTensor_swap12 Y hY h i j k))
    (fun i j k => congrArg (algebraMap L A) (coefficientCubicTensor_swap23 Y hY h i j k)) y Z
  · exact matrixBilinearPairing_radical_map (coefficientHessian Y hY h)
      (coefficientCoordinate (K := K) Y) (coefficientHessian_radial_contraction Y hY h hh)
  · exact tensorTrilinearPairing_radial_map (coefficientHessian Y hY h) (coefficientCubicTensor Y hY h)
      (coefficientCoordinate (K := K) Y) (coefficientCubicTensor_radial_contraction Y hY h hh)
  · exact hZ

end DimensionFourDependence
