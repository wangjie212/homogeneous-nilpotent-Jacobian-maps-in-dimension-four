import DimensionFourDependence.FaithfulCoefficientTensor
import DimensionFourDependence.ProjectiveLineAtlasPoints
import Mathlib.RingTheory.TensorProduct.MvPolynomial
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-! # Polynomial coefficients descend across a relatively closed algebraic extension

Independence gives a linear retraction from the original source field
onto its polynomial coordinate algebra. Extending that retraction to
the coefficient tensor extracts the whole coefficient polynomial.
Faithfulness of the actual tensor realization then descends any
polynomial expansion representing an original source function.
-/

namespace DimensionFourDependence

open MvPolynomial
open scoped TensorProduct

variable {C M E : Type*} [Field C] [Field M] [Field E] [Algebra C M] [Algebra C E] {n : ℕ}

/-- Coefficient base change and the actual tensor polynomial
evaluation retain the same entire polynomial value. -/
theorem scalar_extended_polynomial_tensor_evaluation
    (x : Fin n → M) (z : E ⊗[C] MvPolynomial (Fin n) C) :
    aeval (fun i => (1 : E) ⊗ₜ[C] x i) (algebraTensorAlgEquiv C E z) =
      Algebra.TensorProduct.map (AlgHom.id C E) (aeval x) z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => simp only [map_add, ha, hb]
  | tmul a P =>
    rw [algebraTensorAlgEquiv_tmul, map_smul, aeval_map_algebra_extension,
      MvPolynomial.aeval_one_tmul]
    simp [Algebra.TensorProduct.map_tmul, TensorProduct.smul_tmul']

/-- If an extended polynomial value is an original source element
in the tensor, independence constructs its entire original-field
coefficient polynomial. No finiteness or algebraicity is needed here. -/
theorem independent_polynomial_tensor_value_descends
    (x : Fin n → M) (hx : AlgebraicIndependent C x)
    (P : MvPolynomial (Fin n) E) (y : M)
    (hvalue : aeval (fun i => (1 : E) ⊗ₜ[C] x i) P = (1 : E) ⊗ₜ[C] y) :
    ∃ Q : MvPolynomial (Fin n) C, MvPolynomial.map (algebraMap C E) Q = P := by
  let f : MvPolynomial (Fin n) C →ₗ[C] M := (aeval x).toLinearMap
  have hf : LinearMap.ker f = ⊥ := LinearMap.ker_eq_bot.mpr (algebraicIndependent_iff_injective_aeval.mp hx)
  let ρ := f.leftInverse
  have hρ (Q : MvPolynomial (Fin n) C) : ρ (aeval x Q) = Q :=
    LinearMap.leftInverse_apply_of_inj hf Q
  have htensor (z : E ⊗[C] MvPolynomial (Fin n) C) :
      ρ.lTensor E (Algebra.TensorProduct.map (AlgHom.id C E) (aeval x) z) = z := by
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add a b ha hb => simp only [map_add, ha, hb]
    | tmul a Q => simp only [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, LinearMap.lTensor_tmul, hρ]
  have hleft : ρ.lTensor E (aeval (fun i => (1 : E) ⊗ₜ[C] x i) P) =
      (algebraTensorAlgEquiv C E).symm P := by
    have he := scalar_extended_polynomial_tensor_evaluation x ((algebraTensorAlgEquiv C E).symm P)
    rw [AlgEquiv.apply_symm_apply] at he
    rw [he, htensor]
  have he := congrArg (fun z : E ⊗[C] M => algebraTensorAlgEquiv C E (ρ.lTensor E z)) hvalue
  rw [hleft, AlgEquiv.apply_symm_apply, LinearMap.lTensor_tmul, algebraTensorAlgEquiv_tmul, one_smul] at he
  exact ⟨ρ y, he.symm⟩

attribute [local instance] Algebra.TensorProduct.rightAlgebra

variable {G : Type*} [Field G] [CharZero C] [Algebra.IsAlgebraic C E]
    [Algebra C G] [Algebra M G] [Algebra E G] [IsScalarTower C M G] [IsScalarTower C E G]

/-- An actual polynomial expansion over algebraic coefficients,
representing an original source function, descends coefficient by
coefficient to the relatively closed original base field. -/
theorem relatively_closed_polynomial_expansion_descends
    (hclosed : algebraicClosure C M = ⊥)
    (x : Fin n → M) (hx : AlgebraicIndependent C x)
    (P : MvPolynomial (Fin n) E) (y : M)
    (hvalue : aeval (fun i => algebraMap M G (x i)) P = algebraMap M G y) :
    ∃ Q : MvPolynomial (Fin n) C,
      MvPolynomial.map (algebraMap C E) Q = P ∧ aeval x Q = y := by
  let φ : E ⊗[C] M →ₐ[E] G :=
    (coefficientTensorRealization (C := C) (L := M) (E := E) (κ := G)).comp
      (Algebra.TensorProduct.commRight C E M).toAlgHom
  have hφinj : Function.Injective φ :=
    (coefficientTensorRealization_injective (κ := G) hclosed).comp
      (Algebra.TensorProduct.commRight C E M).injective
  have hφleft (m : M) : φ ((1 : E) ⊗ₜ[C] m) = algebraMap M G m := by
    simp only [φ, AlgHom.comp_apply, AlgEquiv.toAlgHom_apply, Algebra.TensorProduct.commRight_tmul,
      coefficientTensorRealization_left]
  have htensor : aeval (fun i => (1 : E) ⊗ₜ[C] x i) P = (1 : E) ⊗ₜ[C] y := by
    apply hφinj
    rw [comp_aeval_apply, hφleft]
    simp only [hφleft]
    exact hvalue
  obtain ⟨Q, hQ⟩ := independent_polynomial_tensor_value_descends x hx P y htensor
  refine ⟨Q, hQ, ?_⟩
  apply (algebraMap M G).injective
  rw [← hQ, aeval_map_algebra_extension] at hvalue
  exact (comp_aeval_apply x (IsScalarTower.toAlgHom C M G) Q).trans hvalue

end DimensionFourDependence
