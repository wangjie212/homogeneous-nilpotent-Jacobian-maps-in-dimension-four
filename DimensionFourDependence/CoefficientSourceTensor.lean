import DimensionFourDependence.FaithfulCoefficientTensor

/-! # Faithful boundary identities retain their values in the source tensor

The graph coefficient field embeds in the original source. Tensoring
this inclusion with a coefficient field remains injective. Thus boundary
polynomial identities transfer to the source tensor, with nonvanishing
retained as well.
-/

namespace DimensionFourDependence

open MvPolynomial
open scoped TensorProduct

attribute [local instance] Algebra.TensorProduct.rightAlgebra

variable {C L F E : Type*} [Field C] [Field L] [Field F] [Field E]
    [Algebra C L] [Algebra C F] [Algebra C E]

/-- Extending a specified source inclusion by the same coefficient
field preserves the extended coefficient action. -/
noncomputable def coefficientSourceTensorMap (f : L →ₐ[C] F) :
    L ⊗[C] E →ₐ[E] F ⊗[C] E :=
  { (Algebra.TensorProduct.map f (AlgHom.id C E)).toRingHom with
    commutes' := by
      intro c
      change Algebra.TensorProduct.map f (AlgHom.id C E) ((1 : L) ⊗ₜ[C] c) = (1 : F) ⊗ₜ[C] c
      simp }

/-- Tensor extension of a field inclusion is injective. -/
theorem coefficientSourceTensorMap_injective (f : L →ₐ[C] F) :
    Function.Injective (coefficientSourceTensorMap (E := E) f) := by
  let φ := Algebra.TensorProduct.map f (AlgHom.id C E)
  have hφ : φ.toLinearMap = f.toLinearMap.rTensor E := by ext a b; rfl
  change Function.Injective φ.toLinearMap
  rw [hφ]
  exact Module.Flat.rTensor_preserves_injective_linearMap _ f.injective

/-- Polynomial values retain their source values under the actual
coefficient tensor inclusion. -/
theorem coefficientSourceTensorMap_polynomial_value (f : L →ₐ[C] F)
    {σ : Type*} (x : σ → L) (P : MvPolynomial σ E) :
    coefficientSourceTensorMap (E := E) f (aeval (fun i => x i ⊗ₜ[C] (1 : E)) P) =
      aeval (fun i => f (x i) ⊗ₜ[C] (1 : E)) P := by
  rw [comp_aeval_apply]
  rfl

variable {κ : Type*} [Field κ] [CharZero C] [Algebra.IsAlgebraic C E]
    [Algebra C κ] [Algebra L κ] [IsScalarTower C L κ]
    [Algebra E κ] [IsScalarTower C E κ]

/-- A polynomial identity in the actual algebraic boundary values
holds already at the original source values after coefficient extension. -/
theorem coefficient_source_tensor_polynomial_zero_of_boundary_zero
    (f : L →ₐ[C] F) {σ : Type*} (hclosed : algebraicClosure C L = ⊥)
    (x : σ → L) (P : MvPolynomial σ E)
    (hzero : aeval (fun i => algebraMap L κ (x i)) P = 0) :
    aeval (fun i => f (x i) ⊗ₜ[C] (1 : E)) P = 0 := by
  rw [← coefficientSourceTensorMap_polynomial_value f x P,
    coefficient_tensor_polynomial_zero_of_boundary_zero hclosed x P hzero, map_zero]

/-- A nonzero boundary polynomial expression remains nonzero at the
original source values in the coefficient-extended source tensor. -/
theorem coefficient_source_tensor_polynomial_ne_zero_of_boundary_ne_zero
    (f : L →ₐ[C] F) {σ : Type*} (x : σ → L) (P : MvPolynomial σ E)
    (hzero : aeval (fun i => algebraMap L κ (x i)) P ≠ 0) :
    aeval (fun i => f (x i) ⊗ₜ[C] (1 : E)) P ≠ 0 := by
  rw [← coefficientSourceTensorMap_polynomial_value f x P]
  exact (map_ne_zero_iff _ (coefficientSourceTensorMap_injective f)).mpr
    (coefficient_tensor_polynomial_ne_zero_of_boundary_ne_zero x P hzero)

end DimensionFourDependence
