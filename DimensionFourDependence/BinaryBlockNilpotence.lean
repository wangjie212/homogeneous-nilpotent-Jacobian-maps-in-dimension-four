import DimensionFourDependence.Nilpotent

/-! # An original invariant binary output block inherits nilpotence -/

namespace DimensionFourDependence

open Matrix

set_option maxHeartbeats 2000000

variable {R : Type*} [CommRing R] {m n : ℕ}

/-- A split matrix quotient inherits actual nilpotence from its ambient
matrix. The original rectangular intertwiner and right inverse suffice. -/
theorem matrix_isNilpotent_of_split_quotient
    (M : Matrix (Fin n) (Fin n) R) (N : Matrix (Fin m) (Fin m) R)
    (P : Matrix (Fin m) (Fin n) R) (I : Matrix (Fin n) (Fin m) R)
    (hPI : P * I = 1) (hcompat : P * M = N * P) (hM : IsNilpotent M) : IsNilpotent N := by
  have hpow (j : ℕ) : P * M ^ j = N ^ j * P := by
    induction j with
    | zero => simp
    | succ j ih =>
      rw [pow_succ, ← Matrix.mul_assoc, ih, Matrix.mul_assoc, hcompat,
        ← Matrix.mul_assoc, ← pow_succ]
  obtain ⟨k, hk⟩ := hM
  refine ⟨k, ?_⟩
  have he := congrArg (fun A => A * I) (hpow k)
  rw [hk, Matrix.mul_zero, Matrix.zero_mul, Matrix.mul_assoc, hPI, Matrix.mul_one] at he
  exact he.symm

/-- The first two rows form a nilpotent binary quotient when their
last two entries vanish, in the original coefficient ring. -/
theorem leading_binary_block_isNilpotent
    (M : Matrix (Fin 4) (Fin 4) R) (hM : IsNilpotent M)
    (hzero : ∀ i : Fin 2, M (i.castAdd 2) 2 = 0 ∧ M (i.castAdd 2) 3 = 0) :
    IsNilpotent (M.submatrix (Fin.castAdd 2) (Fin.castAdd 2)) := by
  let P : Matrix (Fin 2) (Fin 4) R := Matrix.of ![![1, 0, 0, 0], ![0, 1, 0, 0]]
  have hPI : P * P.transpose = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [P, Matrix.mul_apply, Fin.sum_univ_succ]
  have hcompat : P * M = M.submatrix (Fin.castAdd 2) (Fin.castAdd 2) * P := by
    have hz0 := hzero 0
    have hz1 := hzero 1
    have hcast0 : (0 : Fin 2).castAdd 2 = (0 : Fin 4) := by decide
    have hcast1 : (1 : Fin 2).castAdd 2 = (1 : Fin 4) := by decide
    simp only [hcast0, hcast1] at hz0 hz1
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [P, Matrix.mul_apply, Fin.sum_univ_succ, hz0, hz1]
  exact matrix_isNilpotent_of_split_quotient M _ P P.transpose hPI hcompat hM

end DimensionFourDependence
