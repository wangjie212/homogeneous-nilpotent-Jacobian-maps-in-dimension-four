import DimensionFourDependence.ClosedGaussCoefficientTensor

/-! # Boundary realizations of coefficient tensors are faithful

Relative closedness makes the algebraic coefficient tensor a field.
Every compatible realization of its two factors in a boundary field is
therefore injective. Polynomial identities detected in that boundary
field hold already in the coefficient tensor itself.
-/

namespace DimensionFourDependence

open MvPolynomial
open scoped TensorProduct

attribute [local instance] Algebra.TensorProduct.rightAlgebra

variable {C L E κ : Type*} [Field C] [CharZero C] [Field L] [Field E] [Field κ]
    [Algebra C L] [Algebra C E] [Algebra.IsAlgebraic C E]
    [Algebra C κ] [Algebra L κ] [IsScalarTower C L κ]
    [Algebra E κ] [IsScalarTower C E κ]

/-- The compatible actual coefficient and parameter-extension values
define the actual realization of their tensor in the boundary field. -/
noncomputable def coefficientTensorRealization : L ⊗[C] E →ₐ[E] κ :=
  { (Algebra.TensorProduct.lift (IsScalarTower.toAlgHom C L κ)
      (IsScalarTower.toAlgHom C E κ) (fun _ _ => Commute.all _ _)).toRingHom with
    commutes' := by
      intro x
      change Algebra.TensorProduct.lift (IsScalarTower.toAlgHom C L κ)
        (IsScalarTower.toAlgHom C E κ) _ ((1 : L) ⊗ₜ[C] x) = algebraMap E κ x
      simp }

/-- Original coefficient values retain their exact boundary-field
values under the actual tensor realization. -/
theorem coefficientTensorRealization_left (x : L) :
    coefficientTensorRealization (C := C) (L := L) (E := E) (κ := κ) (x ⊗ₜ[C] (1 : E)) =
      algebraMap L κ x := by
  simp [coefficientTensorRealization]

/-- A boundary realization of an algebraic tensor over a relatively
closed coefficient field is injective. No faithful-evaluation hypothesis
is supplied. -/
theorem coefficientTensorRealization_injective
    (hclosed : algebraicClosure C L = ⊥) :
    Function.Injective (coefficientTensorRealization (C := C) (L := L) (E := E) (κ := κ)) := by
  let : Field (L ⊗[C] E) := (algebraic_tensor_isField_of_relatively_closed hclosed).toField
  exact (coefficientTensorRealization (C := C) (L := L) (E := E) (κ := κ)).injective

/-- Every polynomial identity in actual algebraic boundary values
already holds in the coefficient tensor before boundary realization. -/
theorem coefficient_tensor_polynomial_zero_of_boundary_zero {σ : Type*}
    (hclosed : algebraicClosure C L = ⊥) (x : σ → L) (P : MvPolynomial σ E)
    (hzero : aeval (fun i => algebraMap L κ (x i)) P = 0) :
    aeval (fun i => x i ⊗ₜ[C] (1 : E)) P = 0 := by
  apply coefficientTensorRealization_injective (κ := κ) hclosed
  change coefficientTensorRealization (C := C) (L := L) (E := E) (κ := κ) _ =
    coefficientTensorRealization (C := C) (L := L) (E := E) (κ := κ) 0
  rw [map_zero, comp_aeval_apply]
  simp only [coefficientTensorRealization_left]
  exact hzero

/-- The same faithful tensor comparison preserves nonvanishing
of every actual coefficient-polynomial expression. -/
theorem coefficient_tensor_polynomial_ne_zero_of_boundary_ne_zero {σ : Type*}
    (x : σ → L) (P : MvPolynomial σ E)
    (hzero : aeval (fun i => algebraMap L κ (x i)) P ≠ 0) :
    aeval (fun i => x i ⊗ₜ[C] (1 : E)) P ≠ 0 := by
  intro hz
  have he := congrArg (coefficientTensorRealization (C := C) (L := L) (E := E) (κ := κ)) hz
  rw [map_zero, comp_aeval_apply] at he
  simp only [coefficientTensorRealization_left] at he
  exact hzero he

end DimensionFourDependence
