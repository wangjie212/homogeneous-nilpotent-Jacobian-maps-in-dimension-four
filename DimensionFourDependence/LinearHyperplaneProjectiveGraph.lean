import DimensionFourDependence.ProjectiveCoefficientMorphism
import DimensionFourDependence.ProjectivePrimeCoordinates

/-! # The actual projective graph of the affine hyperplane L = 1

The homogeneous substitution [X] ↦ [L(X) : X] is defined everywhere.
Its infinity hyperplane pulls back exactly to L = 0.
-/

namespace DimensionFourDependence

open MvPolynomial AlgebraicGeometry HomogeneousIdeal

attribute [local instance] MvPolynomial.gradedAlgebra

universe u v

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {E : Type u} {σ : Type v} [Field E]

/-- The original polynomial substitution for the graph [L(X) : X]. -/
noncomputable def linearHyperplaneGraphHom (L : MvPolynomial σ E) :
    MvPolynomial (Option σ) E →ₐ[E] MvPolynomial σ E :=
  aeval (fun j : Option σ => j.elim L X)

theorem linearHyperplaneGraphHom_none (L : MvPolynomial σ E) :
    linearHyperplaneGraphHom L (X none) = L := by
  simp [linearHyperplaneGraphHom]

theorem linearHyperplaneGraphHom_some (L : MvPolynomial σ E) (i : σ) :
    linearHyperplaneGraphHom L (X (some i)) = X i := by
  simp [linearHyperplaneGraphHom]

/-- The graph substitution fixes every original affine polynomial. -/
theorem linearHyperplaneGraphHom_rename (L : MvPolynomial σ E) (P : MvPolynomial σ E) :
    linearHyperplaneGraphHom L (rename some P) = P := by
  have he : (linearHyperplaneGraphHom L).comp (rename some) = AlgHom.id E _ := by
    apply MvPolynomial.algHom_ext
    intro i
    simp [linearHyperplaneGraphHom]
  exact DFunLike.congr_fun he P

/-- A linear form makes the graph substitution preserve each degree. -/
noncomputable def linearHyperplaneGraphGradedHom (L : MvPolynomial σ E) (hL : L.IsHomogeneous 1) :
    homogeneousSubmodule (Option σ) E →+*ᵍ homogeneousSubmodule σ E where
  toRingHom := (linearHyperplaneGraphHom L).toRingHom
  map_mem := by
    intro n P hP
    have hforms (j : Option σ) : (j.elim L X).IsHomogeneous 1 := by
      cases j with
      | none => exact hL
      | some i => exact isHomogeneous_X (R := E) i
    change ((linearHyperplaneGraphHom L) P).IsHomogeneous n
    simpa only [linearHyperplaneGraphHom, one_mul] using hP.aeval _ hforms

/-- The unchanged original variables make the graph morphism defined
at every point, including every point of L = 0. -/
theorem linearHyperplaneGraphGradedHom_irrelevant_le
    (L : MvPolynomial σ E) (hL : L.IsHomogeneous 1) :
    irrelevant (homogeneousSubmodule σ E) ≤
      (irrelevant (homogeneousSubmodule (Option σ) E)).map (linearHyperplaneGraphGradedHom L hL) := by
  apply (HomogeneousIdeal.irrelevant_le _).mpr
  intro i hi P hP
  have hvars : idealOfVars σ E ≤
      ((irrelevant (homogeneousSubmodule (Option σ) E)).map
        (linearHyperplaneGraphGradedHom L hL)).toIdeal := by
    apply Ideal.span_le.mpr
    rintro _ ⟨a, rfl⟩
    have ha : X (some a) ∈ irrelevant (homogeneousSubmodule (Option σ) E) :=
      HomogeneousIdeal.mem_irrelevant_of_mem _ (by omega) (isHomogeneous_X (R := E) (some a))
    change X a ∈ (irrelevant (homogeneousSubmodule (Option σ) E)).toIdeal.map
      (linearHyperplaneGraphHom L).toRingHom
    have hm := Ideal.mem_map_of_mem (linearHyperplaneGraphHom L).toRingHom ha
    change linearHyperplaneGraphHom L (X (some a)) ∈ _ at hm
    rwa [linearHyperplaneGraphHom_some] at hm
  apply hvars
  rw [← pow_one (idealOfVars σ E)]
  apply (mem_pow_idealOfVars_iff 1 P).mpr
  intro m hm
  have hd : m.degree = i := by
    simpa only [Finsupp.degree_eq_weight_one, Pi.one_def] using hP (mem_support_iff.mp hm)
  omega

/-- The actual everywhere-defined projective morphism [X] ↦ [L(X) : X]. -/
noncomputable def linearHyperplaneProjectiveGraph (L : MvPolynomial σ E) (hL : L.IsHomogeneous 1) :
    AlgebraicGeometry.Proj (homogeneousSubmodule σ E) ⟶
      AlgebraicGeometry.Proj (homogeneousSubmodule (Option σ) E) :=
  Proj.map (linearHyperplaneGraphGradedHom L hL) (linearHyperplaneGraphGradedHom_irrelevant_le L hL)

/-- Equation membership in the actual graph is exactly substitution
by L for the homogenizing coordinate, for every polynomial. -/
theorem linearHyperplaneProjectiveGraph_mem_iff
    (L : MvPolynomial σ E) (hL : L.IsHomogeneous 1)
    (z : ProjectiveSpectrum (homogeneousSubmodule σ E)) (P : MvPolynomial (Option σ) E) :
    P ∈ (linearHyperplaneProjectiveGraph L hL z).asHomogeneousIdeal ↔
      linearHyperplaneGraphHom L P ∈ z.asHomogeneousIdeal := Iff.rfl

/-- The affine chart of the graph pulls back to the exact original
denominator open; its complement is the normal hyperplane at infinity. -/
theorem linearHyperplaneProjectiveGraph_preimage_affine_chart
    (L : MvPolynomial σ E) (hL : L.IsHomogeneous 1) :
    linearHyperplaneProjectiveGraph L hL ⁻¹ᵁ
        Proj.basicOpen (homogeneousSubmodule (Option σ) E) (X none) =
      Proj.basicOpen (homogeneousSubmodule σ E) L := by
  change Proj.map _ _ ⁻¹ᵁ _ = _
  rw [Proj.map_preimage_basicOpen]
  change Proj.basicOpen (homogeneousSubmodule σ E) (linearHyperplaneGraphHom L (X none)) = _
  rw [linearHyperplaneGraphHom_none]

end DimensionFourDependence
