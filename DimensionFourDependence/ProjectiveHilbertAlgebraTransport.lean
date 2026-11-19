import DimensionFourDependence.GenericDirectionTangent
import DimensionFourDependence.FiberHilbertDegree

/-! # Hilbert functions retain their coefficients across a specified residue-field isomorphism -/

namespace DimensionFourDependence

open MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra

variable {E C F G σ : Type*} [Field E] [Field C] [Field F] [Field G]
  [Algebra E F] [Algebra E G] [Algebra C F]

/-- Transport the specified coefficient action along the specified
field isomorphism, retaining the original coefficient embedding. -/
@[instance_reducible]
noncomputable def transportedCoefficientAlgebra (φ : F ≃ₐ[E] G) : Algebra C G :=
  (φ.toRingEquiv.toRingHom.comp (algebraMap C F)).toAlgebra

/-- The same field isomorphism then respects the full transported
coefficient field, not only its original subfield. -/
noncomputable def transportedCoefficientAlgEquiv (φ : F ≃ₐ[E] G) :
    letI := transportedCoefficientAlgebra (C := C) φ
    F ≃ₐ[C] G := by
  letI := transportedCoefficientAlgebra (C := C) φ
  exact { φ.toRingEquiv with commutes' := fun _ => rfl }

/-- Transport also preserves the scalar tower of the original constants. -/
theorem transportedCoefficientAlgebra_scalarTower
    [Algebra E C] [IsScalarTower E C F] (φ : F ≃ₐ[E] G) :
    letI := transportedCoefficientAlgebra (C := C) φ
    IsScalarTower E C G := by
  letI := transportedCoefficientAlgebra (C := C) φ
  apply IsScalarTower.of_algebraMap_eq
  intro c
  change algebraMap E G c = φ (algebraMap C F (algebraMap E C c))
  rw [← IsScalarTower.algebraMap_apply E C F, φ.commutes]

/-- Each projective Hilbert-function value is preserved with the
transported coefficient action and exactly the specified coordinate images. -/
theorem projective_hilbert_eq_of_transported_coefficients
    [Finite σ] (φ : F ≃ₐ[E] G) (x : σ → F) (n : ℕ) :
    letI := transportedCoefficientAlgebra (C := C) φ
    projectiveHilbertFunction (projectiveFieldPointIdeal (E := C) (fun i => φ (x i))).toIdeal n =
      projectiveHilbertFunction (projectiveFieldPointIdeal (E := C) x).toIdeal n := by
  letI := transportedCoefficientAlgebra (C := C) φ
  exact congrArg (fun J => projectiveHilbertFunction J n)
    (projectiveFieldPointIdeal_algHom x (transportedCoefficientAlgEquiv (C := C) φ).toAlgHom)

/-- In particular positive curve degree transfers through the same
explicit field and coordinate comparison. -/
theorem projective_curve_degree_iff_of_transported_coefficients
    [Finite σ] (φ : F ≃ₐ[E] G) (x : σ → F) (D : ℕ) :
    letI := transportedCoefficientAlgebra (C := C) φ
    HasCurveHilbertDegree (projectiveFieldPointIdeal (E := C) (fun i => φ (x i))).toIdeal D ↔
      HasCurveHilbertDegree (projectiveFieldPointIdeal (E := C) x).toIdeal D := by
  letI := transportedCoefficientAlgebra (C := C) φ
  simp only [HasCurveHilbertDegree, projective_hilbert_eq_of_transported_coefficients φ x]

/-- A specified coordinate comparison transfers the degree directly
to the prescribed target tuple, with the same transported coefficients. -/
theorem projective_curve_degree_of_transported_coordinates
    [Finite σ] (φ : F ≃ₐ[E] G) (x : σ → F) (y : σ → G)
    (hxy : (fun i => φ (x i)) = y) {D : ℕ}
    (hD : HasCurveHilbertDegree (projectiveFieldPointIdeal (E := C) x).toIdeal D) :
    letI := transportedCoefficientAlgebra (C := C) φ
    HasCurveHilbertDegree (projectiveFieldPointIdeal (E := C) y).toIdeal D := by
  letI := transportedCoefficientAlgebra (C := C) φ
  rw [← hxy]
  exact (projective_curve_degree_iff_of_transported_coefficients (C := C) φ x D).mpr hD

end DimensionFourDependence
