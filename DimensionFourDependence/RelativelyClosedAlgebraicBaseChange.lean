import DimensionFourDependence.RelativelyClosedFiniteBaseChange
import Mathlib.LinearAlgebra.TensorProduct.Finiteness

/-! # Arbitrary algebraic coefficient extensions of the closed source field

Every tensor is a finite sum. Its coefficients lie in a finite intermediate
field, where the preceding finite-extension theorem provides an inverse.
Mapping that inverse to the full tensor product proves that the latter is
a field as well. No finite-degree assumption on the coefficient extension
is needed.
-/

namespace DimensionFourDependence

open scoped TensorProduct

variable {K F L : Type*} [Field K] [Field F] [Field L]
  [Algebra K F] [Algebra K L] [Algebra.IsAlgebraic K L]

/-- A tensor over an algebraic coefficient extension comes from an actual
finite intermediate coefficient field. -/
theorem tensor_mem_finite_intermediate_field (x : F ⊗[K] L) :
    ∃ E : IntermediateField K L, Module.Finite K E ∧
      ∃ y : F ⊗[K] E,
        Algebra.TensorProduct.map (AlgHom.id K F) E.val y = x := by
  classical
  obtain ⟨S, hS⟩ := TensorProduct.exists_finset x
  let U : Finset L := S.image Prod.snd
  let E := IntermediateField.adjoin K (U : Set L)
  have hE : Module.Finite K E :=
    IntermediateField.finiteDimensional_adjoin fun a _ => Algebra.IsIntegral.isIntegral a
  have hmem (a : S) : a.val.2 ∈ E :=
    IntermediateField.subset_adjoin K (U : Set L)
      (Finset.mem_image.mpr ⟨a.val, a.property, rfl⟩)
  let y : F ⊗[K] E := ∑ a : S, a.val.1 ⊗ₜ[K] (⟨a.val.2, hmem a⟩ : E)
  refine ⟨E, hE, y, ?_⟩
  simp only [y, map_sum, Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
  change (∑ a : S, a.val.1 ⊗ₜ[K] a.val.2) = x
  rw [hS]
  apply Finset.sum_bij (fun (a : S) _ => a.val)
  · intro a _
    exact a.property
  · intro a _ b _ hab
    exact Subtype.ext hab
  · intro b hb
    exact ⟨⟨b, hb⟩, Finset.mem_univ _, rfl⟩
  · intro a _
    rfl

variable [CharZero K]

/-- In characteristic zero, arbitrary algebraic coefficient extensions
preserve a relatively closed source extension as an actual tensor field. -/
theorem algebraic_tensor_isField_of_relatively_closed
    (hclosed : algebraicClosure K F = ⊥) : IsField (F ⊗[K] L) := by
  refine ⟨⟨0, 1, zero_ne_one⟩, mul_comm, ?_⟩
  intro x hx
  obtain ⟨E, hE, y, hy⟩ := tensor_mem_finite_intermediate_field x
  let : Module.Finite K E := hE
  let f := Algebra.TensorProduct.map (AlgHom.id K F) E.val
  have hy0 : y ≠ 0 := by
    intro hz
    apply hx
    rw [← hy, hz, map_zero]
  obtain ⟨z, hz⟩ :=
    (finite_separable_tensor_isField_of_relatively_closed (L := E) hclosed).mul_inv_cancel hy0
  refine ⟨f z, ?_⟩
  change x * f z = 1
  rw [← hy, ← map_mul, hz, map_one]

/-- Every algebraic extension of the actual closed Gauss parameter field,
including its algebraic closure, leaves the coefficient-extended source
a field. -/
theorem actual_closed_gauss_cover_algebraic_base_change_isField
    {K' : Type*} [Field K'] [CharZero K']
    (H : Fin 4 → MvPolynomial (Fin 4) K') (I : ImageRelationWitness H)
    (L' : Type*) [Field L'] [Algebra (closedGaussParameterField H I) L']
    [Algebra.IsAlgebraic (closedGaussParameterField H I) L'] :
    IsField (FractionRing (MvPolynomial (Fin 4) K') ⊗[closedGaussParameterField H I] L') := by
  let : CharZero (closedGaussParameterField H I) :=
    charZero_of_injective_algebraMap (algebraMap K' (closedGaussParameterField H I)).injective
  exact algebraic_tensor_isField_of_relatively_closed (closedGaussParameterField_relatively_closed H I)

end DimensionFourDependence
