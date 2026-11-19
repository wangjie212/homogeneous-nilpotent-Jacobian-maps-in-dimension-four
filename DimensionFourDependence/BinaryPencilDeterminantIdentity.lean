import DimensionFourDependence.LinearTameConjugacy

/-! # The determinant factor for a change of binary pencil basis -/

namespace DimensionFourDependence.Shear

open Matrix

variable {R : Type*} [CommRing R]

/-- The two-dimensional alternating matrix acquires exactly the determinant
under congruence by any coefficient matrix. -/
theorem binary_pencil_alternating_matrix_congruence (C : Matrix (Fin 2) (Fin 2) R) :
    let J : Matrix (Fin 2) (Fin 2) R := !![0, 1; -1, 0]
    C * J * Cᵀ = C.det • J := by
  dsimp only
  funext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.det_fin_two, Fin.sum_univ_two] <;> ring

/-- In the new active coordinates, the pencil row is multiplied by the
inverse coordinate matrix and the shear multiplier by the determinant. -/
theorem binary_pencil_shear_coordinate_change
    (C D : Matrix (Fin 2) (Fin 2) R) (hDC : D * C = 1)
    (ℓ v : Fin 2 → R) (c : R) :
    let J : Matrix (Fin 2) (Fin 2) R := !![0, 1; -1, 0]
    let ℓ' := Dᵀ *ᵥ ℓ
    let v' := C *ᵥ v
    C *ᵥ (v + (c * (ℓ ⬝ᵥ v)) • (J *ᵥ ℓ)) =
      v' + ((c * C.det) * (ℓ' ⬝ᵥ v')) • (J *ᵥ ℓ') := by
  let J : Matrix (Fin 2) (Fin 2) R := !![0, 1; -1, 0]
  let ℓ' := Dᵀ *ᵥ ℓ
  let v' := C *ᵥ v
  change C *ᵥ (v + (c * (ℓ ⬝ᵥ v)) • (J *ᵥ ℓ)) =
    v' + ((c * C.det) * (ℓ' ⬝ᵥ v')) • (J *ᵥ ℓ')
  have hℓ : Cᵀ *ᵥ ℓ' = ℓ := by
    change Cᵀ *ᵥ (Dᵀ *ᵥ ℓ) = ℓ
    rw [mulVec_mulVec, ← Matrix.transpose_mul, hDC, Matrix.transpose_one, one_mulVec]
  have hdot : ℓ' ⬝ᵥ v' = ℓ ⬝ᵥ v := by
    change ℓ' ⬝ᵥ (C *ᵥ v) = ℓ ⬝ᵥ v
    have hvec : ℓ' ᵥ* C = ℓ := by
      simpa only [transpose_transpose, vecMul_transpose] using
        (vecMul_transpose Cᵀ ℓ').trans hℓ
    rw [dotProduct_mulVec, hvec]
  have hskew : C *ᵥ (J *ᵥ ℓ) = C.det • (J *ᵥ ℓ') := by
    calc
      C *ᵥ (J *ᵥ ℓ) = (C * J * Cᵀ) *ᵥ ℓ' := by
        rw [← mulVec_mulVec, ← mulVec_mulVec, hℓ]
      _ = C.det • (J *ᵥ ℓ') := by
        rw [binary_pencil_alternating_matrix_congruence, smul_mulVec]
  rw [mulVec_add, mulVec_smul, hskew, smul_smul, hdot]
  rw [mul_right_comm c (ℓ ⬝ᵥ v) C.det]

end DimensionFourDependence.Shear
