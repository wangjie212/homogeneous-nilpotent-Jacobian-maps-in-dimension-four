import DimensionFourDependence.BinaryPencilDeterminantIdentity

/-! # Scalar shear coordinates under an inverse active frame -/

namespace DimensionFourDependence.Shear

open Matrix

variable {R : Type*} [CommRing R]

theorem binary_pencil_scalar_shear_conjugate (T S : Matrix (Fin 2) (Fin 2) R)
    (hTS : T * S = 1) (hST : S * T = 1) (a b c x y : R) :
    let a' := T 0 0 * a + T 1 0 * b
    let b' := T 0 1 * a + T 1 1 * b
    let x' := T 0 0 * x + T 0 1 * y
    let y' := T 1 0 * x + T 1 1 * y
    S *ᵥ ![c * b * (a * x' + b * y'), -(c * a * (a * x' + b * y'))] =
      ![(c * S.det) * b' * (a' * x + b' * y), -((c * S.det) * a' * (a' * x + b' * y))] := by
  let l : Fin 2 → R := ![a, b]
  let v : Fin 2 → R := ![x, y]
  let J : Matrix (Fin 2) (Fin 2) R := !![0, 1; -1, 0]
  have hback : S *ᵥ (T *ᵥ v) = v := by rw [mulVec_mulVec, hST, one_mulVec]
  have he := binary_pencil_shear_coordinate_change S T hTS l (T *ᵥ v) c
  change S *ᵥ (T *ᵥ v + (c * (l ⬝ᵥ (T *ᵥ v))) • (J *ᵥ l)) =
    S *ᵥ (T *ᵥ v) + ((c * S.det) * ((Tᵀ *ᵥ l) ⬝ᵥ (S *ᵥ (T *ᵥ v)))) •
      (J *ᵥ (Tᵀ *ᵥ l)) at he
  rw [mulVec_add, hback] at he
  have h := add_left_cancel he
  have hfirst : (c * (l ⬝ᵥ (T *ᵥ v))) • (J *ᵥ l) =
      ![c * b * (a * (T 0 0 * x + T 0 1 * y) + b * (T 1 0 * x + T 1 1 * y)),
        -(c * a * (a * (T 0 0 * x + T 0 1 * y) + b * (T 1 0 * x + T 1 1 * y)))] := by
    funext i
    fin_cases i <;> simp [l, v, J, mulVec, dotProduct, Fin.sum_univ_two] <;> ring
  rw [hfirst] at h
  funext i
  have hi := congrFun h i
  fin_cases i <;> simp [l, v, J, mulVec, dotProduct, Fin.sum_univ_two] at hi ⊢ <;>
    linear_combination hi

end DimensionFourDependence.Shear
