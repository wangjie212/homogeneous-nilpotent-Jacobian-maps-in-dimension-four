import DimensionFourDependence.LinearPencilProjectiveField
import DimensionFourDependence.IndependentScaleHomogeneousValues

/-! # Characteristic root factorization places every scaled output in its actual parameter field -/

namespace DimensionFourDependence

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {F : Type*} [Field F]

/-- Normalizing the root factorization by the tangent-plane value
leaves exactly a polynomial in the original ratio rho/L_t. -/
theorem root_factorization_normalized_value (r T v w : F) (hT : T ≠ 0)
    {d : ℕ} (hd : 0 < d) :
    r ^ (d - 1) * (r * v + T * w) / T ^ d =
      (r / T) ^ (d - 1) * ((r / T) * v + w) := by
  have hpow : d = (d - 1) + 1 := by omega
  have hTd : T ^ d = T ^ (d - 1) * T := by
    conv_lhs => rw [hpow, pow_succ]
  rw [hTd, div_pow]
  field_simp [hT]
  <;> ring

variable {E : Type*} [Field E] [Algebra E F]

/-- Each normalized characteristic output belongs to the actual
subfield E(rho/L_t), retaining its original component coefficients. -/
theorem root_factorization_normalized_value_mem_parameter_field
    (r T : F) (hT : T ≠ 0) (v w : E) {d : ℕ} (hd : 0 < d) :
    r ^ (d - 1) * (r * algebraMap E F v + T * algebraMap E F w) / T ^ d ∈
      IntermediateField.adjoin E {r / T} := by
  rw [root_factorization_normalized_value r T _ _ hT hd]
  let B := IntermediateField.adjoin E {r / T}
  have ht : r / T ∈ B := IntermediateField.subset_adjoin E _ rfl
  exact B.mul_mem (pow_mem ht (d - 1)) (B.add_mem (B.mul_mem ht (B.algebraMap_mem v)) (B.algebraMap_mem w))

/-- After adjoining the independent scale, every actual root-factored
output belongs to E(rho/L_t)(s) in the same source realization. -/
theorem root_factorization_scaled_output_mem_parameter_scale_field
    (r T : F) (hT : T ≠ 0) (v w : E) {d : ℕ} (hd : 0 < d) :
    (RatFunc.X : RatFunc F) ^ d * RatFunc.C
      (r ^ (d - 1) * (r * algebraMap E F v + T * algebraMap E F w) / T ^ d) ∈
      IntermediateField.adjoin (IntermediateField.adjoin E {r / T}) {(RatFunc.X : RatFunc F)} := by
  let B := IntermediateField.adjoin E {r / T}
  let J := IntermediateField.adjoin B {(RatFunc.X : RatFunc F)}
  let b : B := ⟨r ^ (d - 1) * (r * algebraMap E F v + T * algebraMap E F w) / T ^ d,
    root_factorization_normalized_value_mem_parameter_field r T hT v w hd⟩
  have hconstant : RatFunc.C (b : F) ∈ J := by
    have he : algebraMap B (RatFunc F) b ∈ J := J.algebraMap_mem b
    rw [IsScalarTower.algebraMap_apply B F (RatFunc F), RatFunc.algebraMap_eq_C] at he
    exact he
  have hX : (RatFunc.X : RatFunc F) ∈ J := IntermediateField.subset_adjoin B _ rfl
  have hXd : (RatFunc.X : RatFunc F) ^ d ∈ J := pow_mem hX d
  exact J.mul_mem hXd hconstant

end DimensionFourDependence
