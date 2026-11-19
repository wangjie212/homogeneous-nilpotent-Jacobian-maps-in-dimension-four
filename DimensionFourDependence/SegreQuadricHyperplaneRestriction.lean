import DimensionFourDependence.SegreProjectiveRulingCoordinates
import DimensionFourDependence.SegreRulingBinaryPolynomial

/-! # Restrict an original matrix-space hyperplane to either actual Segre ruling -/

namespace DimensionFourDependence

open Matrix

set_option maxHeartbeats 2000000

variable {F : Type*} [Field F]

/-- The exact two coefficients of an original matrix hyperplane on
the specified ruling, in radial-then-varying coordinate order. -/
def segreQuadricRulingBinaryCoefficients (j : Fin 3) (t : F) (A : Fin 4 → F) : Fin 2 → F :=
  ![A 0 + t * A j.castSucc, A (segreRulingRemainingIndex j).castSucc + t * A 3]

/-- A specified field embedding retains every coefficient of the
original hyperplane's actual ruling restriction. -/
theorem segreQuadricRulingBinaryCoefficients_map {G : Type*} [Field G]
    (φ : F →+* G) (j : Fin 3) (t : F) (A : Fin 4 → F) (i : Fin 2) :
    segreQuadricRulingBinaryCoefficients j (φ t) (fun k => φ (A k)) i =
      φ (segreQuadricRulingBinaryCoefficients j t A i) := by
  fin_cases i <;> simp [segreQuadricRulingBinaryCoefficients, map_add, map_mul]

/-- A hyperplane restricts exactly to its binary form on every vector
of the actual ruling kernel, including infinity representatives. -/
theorem segre_quadric_ruling_hyperplane_binary_pairing
    (j : Fin 3) (hj : j ≠ 0) (t : F) (A Y : Fin 4 → F)
    (hkernel : segreRulingMatrix j t *ᵥ Y = 0) :
    A ⬝ᵥ Y = segreQuadricRulingBinaryCoefficients j t A 0 * Y 0 +
      segreQuadricRulingBinaryCoefficients j t A 1 * Y (segreRulingRemainingIndex j).castSucc := by
  have h0 := congrFun hkernel 0
  have h1 := congrFun hkernel 1
  rw [segreRulingMatrix_mulVec] at h0 h1
  fin_cases j
  · exact False.elim (hj rfl)
  · change Y 1 - t * Y 0 = 0 at h0
    change Y 3 - t * Y 2 = 0 at h1
    simp [segreQuadricRulingBinaryCoefficients, segreRulingRemainingIndex,
      dotProduct, Fin.sum_univ_succ, sub_eq_zero.mp h0, sub_eq_zero.mp h1]
    ring
  · change Y 2 - t * Y 0 = 0 at h0
    change Y 3 - t * Y 1 = 0 at h1
    simp [segreQuadricRulingBinaryCoefficients, segreRulingRemainingIndex,
      dotProduct, Fin.sum_univ_succ, sub_eq_zero.mp h0, sub_eq_zero.mp h1]
    ring

/-- The original generic output has the very same exact binary
hyperplane restriction, derived from its original quadric equation. -/
theorem segre_output_hyperplane_binary_pairing
    (Y : Fin 4 → F) (hY0 : Y 0 ≠ 0) (hSegre : Y 0 * Y 3 - Y 1 * Y 2 = 0)
    (j : Fin 3) (hj : j ≠ 0) (A : Fin 4 → F) :
    A ⬝ᵥ Y = segreQuadricRulingBinaryCoefficients j (Y j.castSucc / Y 0) A 0 * Y 0 +
      segreQuadricRulingBinaryCoefficients j (Y j.castSucc / Y 0) A 1 *
        Y (segreRulingRemainingIndex j).castSucc :=
  segre_quadric_ruling_hyperplane_binary_pairing j hj _ A Y
    (segre_output_mem_ruling_kernel Y hY0 hSegre j hj)

end DimensionFourDependence
