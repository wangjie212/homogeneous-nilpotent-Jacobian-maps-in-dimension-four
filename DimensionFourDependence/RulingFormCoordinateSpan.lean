import DimensionFourDependence.MatrixKernelScalarExtension
import Mathlib.LinearAlgebra.Dual.Lemmas

/-! # Two independent ruling forms express every original coordinate, after any field extension -/

namespace DimensionFourDependence

open Matrix Module

variable {F : Type*} [Field F] {n m : ℕ}

/-- Restriction of an original covector to an actual vector ruling. -/
noncomputable def rulingFormRestriction (W : Submodule F (Fin n → F)) (c : Fin n → F) :
    Module.Dual F W := (dotProductBilin F F c).comp W.subtype

/-- On a two-dimensional ruling, two independent original forms
give coefficient expressions for every original coordinate. The two
coefficient vectors are constructed from the dual basis. -/
theorem two_dimensional_ruling_coordinate_form_span
    (W : Submodule F (Fin n → F)) (hdim : finrank F W = 2) (s t : Fin n → F)
    (hpair : LinearIndependent F ![rulingFormRestriction W s, rulingFormRestriction W t]) :
    ∃ bS bN : Fin n → F, ∀ x ∈ W, ∀ i,
      x i = bS i * (s ⬝ᵥ x) + bN i * (t ⬝ᵥ x) := by
  have hcard : Fintype.card (Fin 2) = finrank F (Module.Dual F W) := by
    rw [Subspace.dual_finrank_eq, hdim]
    rfl
  let B := basisOfLinearIndependentOfCardEqFinrank hpair hcard
  let c : Fin n → Module.Dual F W := fun i => (LinearMap.proj i).comp W.subtype
  have hB0 : B 0 = rulingFormRestriction W s := congrFun
    (coe_basisOfLinearIndependentOfCardEqFinrank hpair hcard) 0
  have hB1 : B 1 = rulingFormRestriction W t := congrFun
    (coe_basisOfLinearIndependentOfCardEqFinrank hpair hcard) 1
  refine ⟨fun i => B.repr (c i) 0, fun i => B.repr (c i) 1, ?_⟩
  intro x hx i
  have hv := LinearMap.congr_fun (B.sum_repr (c i)) ⟨x, hx⟩
  simp only [Fin.sum_univ_two, LinearMap.add_apply, LinearMap.smul_apply] at hv
  rw [hB0, hB1] at hv
  exact hv.symm

variable {E : Type*} [Field E] [Algebra F E]

/-- Coordinate-form relations on the original matrix kernel remain
valid at every point of its scalar extension, with the same coefficient
vectors. No extended-kernel spanning data are assumed. -/
theorem matrix_kernel_coordinate_form_span_after_extension
    (A : Matrix (Fin m) (Fin n) F) (s t bS bN : Fin n → F)
    (hspan : ∀ x ∈ LinearMap.ker A.toLin', ∀ i,
      x i = bS i * (s ⬝ᵥ x) + bN i * (t ⬝ᵥ x))
    (y : Fin n → E) (hy : A.map (algebraMap F E) *ᵥ y = 0) :
    ∀ i, y i = algebraMap F E (bS i) * ((fun j => algebraMap F E (s j)) ⬝ᵥ y) +
      algebraMap F E (bN i) * ((fun j => algebraMap F E (t j)) ⬝ᵥ y) := by
  let R : Matrix (Fin n) (Fin n) F := 1 - vecMulVec bS s - vecMulVec bN t
  have hker : LinearMap.ker A.toLin' ≤ LinearMap.ker R.toLin' := by
    intro x hx
    change R *ᵥ x = 0
    dsimp only [R]
    rw [sub_mulVec, sub_mulVec, one_mulVec, vecMulVec_mulVec, vecMulVec_mulVec]
    funext i
    change x i - bS i * (s ⬝ᵥ x) - bN i * (t ⬝ᵥ x) = 0
    rw [hspan x hx i]
    ring
  have hRy := matrix_kernel_le_after_scalar_extension (E := E) A R hker
    (show y ∈ LinearMap.ker (A.map (algebraMap F E)).toLin' from hy)
  have hmap : R.map (algebraMap F E) = 1 -
      vecMulVec (fun i => algebraMap F E (bS i)) (fun i => algebraMap F E (s i)) -
      vecMulVec (fun i => algebraMap F E (bN i)) (fun i => algebraMap F E (t i)) := by
    ext i j
    simp [R, Matrix.map_apply, Matrix.vecMulVec, Matrix.one_apply]
  change R.map (algebraMap F E) *ᵥ y = 0 at hRy
  rw [hmap, sub_mulVec, sub_mulVec, one_mulVec, vecMulVec_mulVec, vecMulVec_mulVec] at hRy
  intro i
  have hi := congrFun hRy i
  change y i - algebraMap F E (bS i) * ((fun j => algebraMap F E (s j)) ⬝ᵥ y) -
    algebraMap F E (bN i) * ((fun j => algebraMap F E (t j)) ⬝ᵥ y) = 0 at hi
  linear_combination hi

/-- Two independent forms on a two-dimensional original matrix
kernel supply the original-coordinate expressions for every actual
scalar-extended ruling point. -/
theorem two_dimensional_matrix_kernel_coordinate_form_span_after_extension
    (A : Matrix (Fin m) (Fin n) F) (hdim : finrank F (LinearMap.ker A.toLin') = 2)
    (s t : Fin n → F)
    (hpair : LinearIndependent F ![rulingFormRestriction (LinearMap.ker A.toLin') s,
      rulingFormRestriction (LinearMap.ker A.toLin') t]) :
    ∃ bS bN : Fin n → F, ∀ y : Fin n → E, A.map (algebraMap F E) *ᵥ y = 0 →
      ∀ i, y i = algebraMap F E (bS i) * ((fun j => algebraMap F E (s j)) ⬝ᵥ y) +
        algebraMap F E (bN i) * ((fun j => algebraMap F E (t j)) ⬝ᵥ y) := by
  obtain ⟨bS, bN, hspan⟩ := two_dimensional_ruling_coordinate_form_span
    (LinearMap.ker A.toLin') hdim s t hpair
  exact ⟨bS, bN, fun y hy => matrix_kernel_coordinate_form_span_after_extension A s t bS bN hspan y hy⟩

end DimensionFourDependence
