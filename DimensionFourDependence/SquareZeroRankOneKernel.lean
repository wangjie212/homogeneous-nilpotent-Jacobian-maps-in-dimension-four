import DimensionFourDependence.RankOneUpdateTrace
import DimensionFourDependence.NilpotentCubicFlag

/-! # A rank-three nilpotent update of a square-zero block constructs a nonzero kernel vector -/

namespace DimensionFourDependence

open Matrix

set_option maxHeartbeats 4000000

variable {F : Type*} [Field F]

/-- Rank three forces the update column's image under a square-zero
base matrix to be nonzero when the update's own scalar pairing is zero. -/
theorem rank_three_square_zero_update_column_image_ne_zero
    (A : Matrix (Fin 4) (Fin 4) F) (c l : Fin 4 → F)
    (hA : A * A = 0) (hlc : l ⬝ᵥ c = 0)
    (hrank : (A + Matrix.vecMulVec c l).rank = 3) : A *ᵥ c ≠ 0 := by
  intro hz
  let B := Matrix.vecMulVec c l
  have hAB : A * B = 0 := by dsimp only [B]; rw [Matrix.mul_vecMulVec, hz]; simp
  have hBB : B * B = 0 := by dsimp only [B]; rw [Matrix.vecMulVec_mul_vecMulVec, hlc]; simp
  have hN2 : (A + B) ^ 2 = B * A := by
    rw [pow_two, add_mul, mul_add, mul_add, hA, hAB, hBB]
    simp
  have hN3 : (A + B) ^ 3 = 0 := by
    rw [show (3 : ℕ) = 2 + 1 from rfl, pow_succ, hN2, mul_add, mul_assoc,
      hA, mul_zero, mul_assoc, hAB, mul_zero, add_zero]
  exact rank_three_matrix_cube_ne_zero (A + B) hrank hN3

variable [CharZero F]

/-- Nilpotence supplies both update pairings, so A*c is a nonzero
actual kernel vector for every rank-three update of a trace-zero
square-zero four-by-four base matrix. -/
theorem nilpotent_rank_three_square_zero_update_constructs_kernel_direction
    (A : Matrix (Fin 4) (Fin 4) F) (c l : Fin 4 → F)
    (hA : A * A = 0) (htrace : Matrix.trace A = 0)
    (hN : IsNilpotent (A + Matrix.vecMulVec c l))
    (hrank : (A + Matrix.vecMulVec c l).rank = 3) :
    A *ᵥ c ≠ 0 ∧ (A + Matrix.vecMulVec c l) *ᵥ (A *ᵥ c) = 0 := by
  have hp := nilpotent_rank_one_update_pairings A c l
    (by rw [hA, htrace]; simp) hN
  have hlc : l ⬝ᵥ c = 0 := by simpa only [htrace, neg_zero] using hp.1
  have hlAc : l ⬝ᵥ (A *ᵥ c) = 0 := by simpa only [htrace, neg_zero, zero_pow (by decide : (2 : ℕ) ≠ 0)] using hp.2
  refine ⟨rank_three_square_zero_update_column_image_ne_zero A c l hA hlc hrank, ?_⟩
  rw [Matrix.add_mulVec, Matrix.mulVec_mulVec, hA, Matrix.zero_mulVec,
    Matrix.vecMulVec_mulVec, hlAc]
  simp

end DimensionFourDependence
