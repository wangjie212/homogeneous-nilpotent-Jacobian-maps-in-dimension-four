import DimensionFourDependence.ConeParameterJacobianSlope

/-! # The proportional-direction cone block is square-zero and its update-column image is explicit -/

namespace DimensionFourDependence

open Matrix

set_option maxHeartbeats 4000000

variable {F : Type*} [Field F]

/-- The full fixed-parameter cone block acts only through the
projected source-coordinate part of an arbitrary vector. -/
theorem cone_fixed_parameter_jacobian_mul_vector
    (V fx hx : Fin 3 → F) (u : Fin 4 → F) :
    coneFixedParameterJacobian V fx hx *ᵥ u =
      Fin.snoc (fun i => V i * (fx ⬝ᵥ (fun j : Fin 3 => u j.castSucc)))
        (hx ⬝ᵥ (fun j : Fin 3 => u j.castSucc)) := by
  funext i
  fin_cases i <;>
    simp [coneFixedParameterJacobian, Matrix.mulVec, dotProduct, Fin.sum_univ_succ,
      Fin.snoc, Fin.castPred, Fin.castLT] <;> ring

/-- If both fixed-parameter output derivatives vanish along the
directrix, the entire original four-by-four cone block is square-zero. -/
theorem cone_fixed_parameter_jacobian_square_zero
    (V fx hx : Fin 3 → F) (hfV : fx ⬝ᵥ V = 0) (hhV : hx ⬝ᵥ V = 0) :
    coneFixedParameterJacobian V fx hx * coneFixedParameterJacobian V fx hx = 0 := by
  let K := coneFixedParameterJacobian V fx hx
  have hcol (j : Fin 4) : (fun k : Fin 3 => K k.castSucc j) = ((Fin.snoc fx (0 : F) : Fin 4 → F) j) • V := by
    funext k
    fin_cases k <;> fin_cases j <;>
      simp [K, coneFixedParameterJacobian, Fin.snoc, Fin.castPred, Fin.castLT, smul_eq_mul, mul_comm] <;> ring
  apply Matrix.ext
  intro i j
  change (K *ᵥ (fun k => K k j)) i = 0
  rw [cone_fixed_parameter_jacobian_mul_vector, hcol, dotProduct_smul, dotProduct_smul, hfV, hhV]
  simp only [smul_zero]
  refine Fin.lastCases ?_ (fun i => ?_) i <;> simp only [Fin.snoc_last, Fin.snoc_castSucc, mul_zero]

/-- In the proportional-direction case, the parameter derivative
of the scalar f cancels from K*c. Its remaining entries use only f,
the two fixed gradients and the actual directrix derivative. -/
theorem square_zero_cone_block_mul_parameter_column
    (V W fx hx : Fin 3 → F) (q f h : F)
    (hfV : fx ⬝ᵥ V = 0) (hhV : hx ⬝ᵥ V = 0) :
    coneFixedParameterJacobian V fx hx *ᵥ Fin.snoc (fun i => q * V i + f * W i) h =
      Fin.snoc (fun i => f * (fx ⬝ᵥ W) * V i) (f * (hx ⬝ᵥ W)) := by
  rw [cone_fixed_parameter_jacobian_mul_vector]
  have hc : (fun j : Fin 3 => (Fin.snoc (fun i => q * V i + f * W i) h : Fin 4 → F) j.castSucc) =
      q • V + f • W := by funext j; simp only [Fin.snoc_castSucc, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [hc, dotProduct_add, dotProduct_add, dotProduct_smul, dotProduct_smul,
    dotProduct_smul, dotProduct_smul, hfV, hhV]
  simp only [smul_eq_mul, mul_zero, zero_add]
  funext i
  refine Fin.lastCases ?_ (fun i => ?_) i
  · rw [Fin.snoc_last, Fin.snoc_last]
  · rw [Fin.snoc_castSucc, Fin.snoc_castSucc]
    ring

end DimensionFourDependence
