import DimensionFourDependence.Nilpotent

/-! # The two trace identities for the cone Jacobian's rank-one update

The parameter-dependent Jacobian is a fixed-parameter matrix plus one
outer product. Expanding its trace and squared trace derives the two
scalar identities used in (4.8) from nilpotence, whenever the base matrix
has zero second characteristic coefficient.
-/

namespace DimensionFourDependence

open Matrix

set_option maxHeartbeats 3000000

variable {R : Type*} [CommRing R] {n : Type*} [Fintype n] [DecidableEq n]

omit [DecidableEq n] in
/-- The trace of a parameter rank-one update is its exact scalar pairing. -/
theorem matrix_rank_one_update_trace (A : Matrix n n R) (c l : n → R) :
    Matrix.trace (A + Matrix.vecMulVec c l) = Matrix.trace A + l ⬝ᵥ c := by
  rw [Matrix.trace_add, Matrix.trace_vecMulVec, dotProduct_comm]

/-- The full square-trace expansion of the parameter rank-one update. -/
theorem matrix_rank_one_update_square_trace (A : Matrix n n R) (c l : n → R) :
    Matrix.trace ((A + Matrix.vecMulVec c l) * (A + Matrix.vecMulVec c l)) =
      Matrix.trace (A * A) + 2 * (l ⬝ᵥ (A *ᵥ c)) + (l ⬝ᵥ c) ^ 2 := by
  have hleft : Matrix.trace (A * Matrix.vecMulVec c l) = l ⬝ᵥ (A *ᵥ c) := by
    rw [Matrix.mul_vecMulVec, Matrix.trace_vecMulVec, dotProduct_comm]
  have hright : Matrix.trace (Matrix.vecMulVec c l * A) = l ⬝ᵥ (A *ᵥ c) := by
    rw [Matrix.trace_mul_comm]
    exact hleft
  have houter : Matrix.trace (Matrix.vecMulVec c l * Matrix.vecMulVec c l) = (l ⬝ᵥ c) ^ 2 := by
    rw [Matrix.vecMulVec_mul_vecMulVec, Matrix.trace_vecMulVec, dotProduct_smul, dotProduct_comm c l]
    simp only [smul_eq_mul, pow_two]
  rw [add_mul, mul_add, mul_add]
  simp only [Matrix.trace_add, hleft, hright, houter]
  ring

variable [IsDomain R] [CharZero R]

/-- Zero trace and zero square trace derive both parameter-update
pairings when the fixed-parameter part has zero second coefficient. -/
theorem matrix_rank_one_update_zero_traces_pairings
    (A : Matrix n n R) (c l : n → R)
    (hbase : Matrix.trace (A * A) = Matrix.trace A ^ 2)
    (htrace : Matrix.trace (A + Matrix.vecMulVec c l) = 0)
    (hsquare : Matrix.trace ((A + Matrix.vecMulVec c l) * (A + Matrix.vecMulVec c l)) = 0) :
    l ⬝ᵥ c = -Matrix.trace A ∧ l ⬝ᵥ (A *ᵥ c) = -(Matrix.trace A) ^ 2 := by
  rw [matrix_rank_one_update_trace] at htrace
  have hfirst : l ⬝ᵥ c = -Matrix.trace A := by linear_combination htrace
  rw [matrix_rank_one_update_square_trace, hbase, hfirst] at hsquare
  have he : (2 : R) * (l ⬝ᵥ (A *ᵥ c) + Matrix.trace A ^ 2) = 0 := by
    linear_combination hsquare
  have hz := (mul_eq_zero.mp he).resolve_left (by norm_num : (2 : R) ≠ 0)
  exact ⟨hfirst, by linear_combination hz⟩

/-- Nilpotence supplies the two actual trace identities in (4.8). -/
theorem nilpotent_rank_one_update_pairings
    (A : Matrix n n R) (c l : n → R)
    (hbase : Matrix.trace (A * A) = Matrix.trace A ^ 2)
    (hN : IsNilpotent (A + Matrix.vecMulVec c l)) :
    l ⬝ᵥ c = -Matrix.trace A ∧ l ⬝ᵥ (A *ᵥ c) = -(Matrix.trace A) ^ 2 := by
  apply matrix_rank_one_update_zero_traces_pairings A c l hbase
  · exact (Matrix.isNilpotent_trace_of_isNilpotent hN).eq_zero
  · have hnil : IsNilpotent ((A + Matrix.vecMulVec c l) * (A + Matrix.vecMulVec c l)) := by
      rw [← pow_two]
      exact hN.pow_of_pos (by decide : (2 : ℕ) ≠ 0)
    exact (Matrix.isNilpotent_trace_of_isNilpotent hnil).eq_zero

end DimensionFourDependence
