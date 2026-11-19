import DimensionFourDependence.BoundaryRationalRootTensor

/-! # Source coefficient identities return to the same algebraic boundary

Faithfulness of both coefficient-tensor realizations preserves the
entire source equation and the original denominator. In particular a
cleared source root identity constructs its actual rational boundary
root rather than assuming a root in that boundary field.
-/

namespace DimensionFourDependence

open MvPolynomial
open scoped TensorProduct

attribute [local instance] Algebra.TensorProduct.rightAlgebra

variable {C L F E κ : Type*} [Field C] [CharZero C] [Field L] [Field F] [Field E] [Field κ]
    [Algebra C L] [Algebra C F] [Algebra C E] [Algebra.IsAlgebraic C E]
    [Algebra C κ] [Algebra L κ] [IsScalarTower C L κ]
    [Algebra E κ] [IsScalarTower C E κ]

/-- An identity of original coefficient polynomials holds in the
source tensor exactly when it holds under its compatible boundary
realization. Both implications retain the specified maps. -/
theorem coefficient_source_tensor_polynomial_zero_iff_boundary_zero
    (f : L →ₐ[C] F) {σ : Type*} (hclosed : algebraicClosure C L = ⊥)
    (x : σ → L) (P : MvPolynomial σ E) :
    aeval (fun i => f (x i) ⊗ₜ[C] (1 : E)) P = 0 ↔
      aeval (fun i => algebraMap L κ (x i)) P = 0 := by
  constructor
  · intro hzero
    have hcoeff : aeval (fun i => x i ⊗ₜ[C] (1 : E)) P = 0 := by
      apply coefficientSourceTensorMap_injective (E := E) f
      rw [coefficientSourceTensorMap_polynomial_value, map_zero]
      exact hzero
    have he := congrArg (coefficientTensorRealization (C := C) (L := L) (E := E) (κ := κ)) hcoeff
    rw [map_zero, comp_aeval_apply] at he
    simpa only [coefficientTensorRealization_left] using he
  · exact coefficient_source_tensor_polynomial_zero_of_boundary_zero f hclosed x P

/-- A cleared root identity in the actual source tensor and its
nonzero denominator construct the rational root power and product
identities in the same original boundary coefficient field. -/
theorem source_tensor_cleared_root_constructs_same_boundary_root
    (f : L →ₐ[C] F) (hclosed : algebraicClosure C L = ⊥)
    {r : ℕ} (n m s : Fin r → E) (y : Fin r → L) (c : L) (d : ℕ)
    (hm : coefficientTensorLinearValue (C := C) m (fun i => f (y i)) ≠ 0)
    (hclear : (coefficientTensorLinearValue (C := C) n (fun i => f (y i)) *
        (f c ⊗ₜ[C] (1 : E))) ^ d =
      coefficientTensorLinearValue (C := C) s (fun i => f (y i)) *
        coefficientTensorLinearValue (C := C) m (fun i => f (y i)) ^ d) :
    let v := fun a : Fin r → E => ∑ i, algebraMap E κ (a i) * algebraMap L κ (y i)
    v m ≠ 0 ∧ (v n * algebraMap L κ c / v m) ^ d = v s ∧
      v m * (v n * algebraMap L κ c / v m) = v n * algebraMap L κ c := by
  classical
  let v := fun a : Fin r → E => ∑ i, algebraMap E κ (a i) * algebraMap L κ (y i)
  let φ := coefficientTensorRealization (C := C) (L := L) (E := E) (κ := κ)
  have hv (a : Fin r → E) : φ (coefficientTensorLinearValue (C := C) a y) = v a :=
    coefficientTensorRealization_linear_value a y
  have hleft (a : L) : coefficientSourceTensorMap (E := E) f (a ⊗ₜ[C] (1 : E)) =
      f a ⊗ₜ[C] (1 : E) := rfl
  have hmκ : v m ≠ 0 := by
    intro hz
    have hc : coefficientTensorLinearValue (C := C) m y = 0 := by
      apply coefficientTensorRealization_injective (κ := κ) hclosed
      rw [map_zero, hv]
      exact hz
    apply hm
    rw [← coefficientSourceTensorMap_linear_value f m y, hc, map_zero]
  have hc : (coefficientTensorLinearValue (C := C) n y * (c ⊗ₜ[C] (1 : E))) ^ d =
      coefficientTensorLinearValue (C := C) s y * coefficientTensorLinearValue (C := C) m y ^ d := by
    apply coefficientSourceTensorMap_injective (E := E) f
    simpa only [map_pow, map_mul, coefficientSourceTensorMap_linear_value, hleft] using hclear
  have hκ : (v n * algebraMap L κ c) ^ d = v s * v m ^ d := by
    have he := congrArg φ hc
    have hφc : φ (c ⊗ₜ[C] (1 : E)) = algebraMap L κ c := coefficientTensorRealization_left c
    simpa only [map_pow, map_mul, hv, hφc] using he
  refine ⟨hmκ, ?_, ?_⟩
  · rw [div_pow, div_eq_iff (pow_ne_zero d hmκ)]
    exact hκ
  · rw [mul_comm (v m), div_mul_cancel₀ _ hmκ]

end DimensionFourDependence
