import DimensionFourDependence.ScalarExtensionRank

/-! # Homogeneous polynomial pieces commute with extension of the coefficient field -/

namespace DimensionFourDependence

open MvPolynomial TensorProduct Module

variable {L : Type*} [Field L] (E : Type*) [Field E] [Algebra L E] {σ : Type*}

/-- The scalar-extension map on one homogeneous polynomial piece. -/
noncomputable def homogeneousScalarExtensionMap (d : ℕ) :
    E ⊗[L] (homogeneousSubmodule σ L d) →ₗ[E] MvPolynomial σ E :=
  (MvPolynomial.algebraTensorAlgEquiv L E).toLinearMap.comp
    ((homogeneousSubmodule σ L d).subtype.baseChange E)

theorem homogeneousScalarExtensionMap_tmul (d : ℕ) (a : E) (p : homogeneousSubmodule σ L d) :
    homogeneousScalarExtensionMap E d (a ⊗ₜ[L] p) =
      a • MvPolynomial.map (algebraMap L E) (p : MvPolynomial σ L) := by
  simp [homogeneousScalarExtensionMap, LinearMap.baseChange_tmul]

theorem homogeneousScalarExtensionMap_injective (d : ℕ) :
    Function.Injective (homogeneousScalarExtensionMap (L := L) (σ := σ) E d) := by
  have hf : Function.Injective ((homogeneousSubmodule σ L d).subtype.baseChange E) :=
    Module.Flat.lTensor_preserves_injective_linearMap _ Subtype.val_injective
  exact (MvPolynomial.algebraTensorAlgEquiv L E).injective.comp hf

/-- The image is exactly the homogeneous piece over the extended field. -/
theorem homogeneousScalarExtensionMap_range (d : ℕ) :
    LinearMap.range (homogeneousScalarExtensionMap (L := L) (σ := σ) E d) =
      homogeneousSubmodule σ E d := by
  classical
  apply le_antisymm
  · rintro _ ⟨z, rfl⟩
    induction z using TensorProduct.inductionOn with
    | tmul a p =>
      rw [homogeneousScalarExtensionMap_tmul]
      exact (homogeneousSubmodule σ E d).smul_mem a (p.property.map (algebraMap L E))
    | add z w hz hw =>
      rw [map_add]
      exact (homogeneousSubmodule σ E d).add_mem hz hw
  · intro p hp
    rw [p.as_sum]
    apply (LinearMap.range (homogeneousScalarExtensionMap E d)).sum_mem
    intro m hm
    have hmdeg : m.degree = d := by
      simpa only [Finsupp.degree_apply] using (hp.degree_eq_sum_deg_support hm).symm
    have hmono : (monomial m (1 : L)).IsHomogeneous d := by
      rw [← hmdeg]
      exact isHomogeneous_monomial 1 rfl
    refine ⟨p.coeff m ⊗ₜ[L] ⟨monomial m (1 : L), hmono⟩, ?_⟩
    rw [homogeneousScalarExtensionMap_tmul]
    simp [smul_monomial, smul_eq_mul]

/-- The canonical homogeneous-piece scalar-extension isomorphism. -/
noncomputable def homogeneousBaseChangeEquiv (d : ℕ) :
    E ⊗[L] (homogeneousSubmodule σ L d) ≃ₗ[E] homogeneousSubmodule σ E d :=
  (LinearEquiv.ofInjective (homogeneousScalarExtensionMap E d)
    (homogeneousScalarExtensionMap_injective E d)).trans
      (LinearEquiv.ofEq _ _ (homogeneousScalarExtensionMap_range E d))

theorem homogeneousBaseChangeEquiv_tmul (d : ℕ) (a : E) (p : homogeneousSubmodule σ L d) :
    (homogeneousBaseChangeEquiv E d (a ⊗ₜ[L] p) : MvPolynomial σ E) =
      a • MvPolynomial.map (algebraMap L E) (p : MvPolynomial σ L) :=
  homogeneousScalarExtensionMap_tmul E d a p

end DimensionFourDependence
