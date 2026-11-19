import DimensionFourDependence.SchemeModuleCategoricalFrames
import DimensionFourDependence.ProjectivePullbackHyperplaneSheaf
import DimensionFourDependence.PolynomialProjectiveProperties

/-! # Actual categorical hyperplane-frame isomorphisms on each inverse chart -/

namespace DimensionFourDependence

open MvPolynomial AlgebraicGeometry CategoryTheory Opposite

attribute [local instance] MvPolynomial.gradedAlgebra

universe u
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 125000

variable {k : Type u} [Field k]
local notation "G" => homogeneousSubmodule (Fin 4) k
local notation "P₃" => Proj G
local notation "U" a:max => Proj.basicOpen G (X a)

theorem identity_projective_chart_nonempty (a : Fin 4) : Nonempty ((𝟙 P₃) ⁻¹ᵁ U a) := by
  refine ⟨⟨polynomialProjectiveGenericPoint k, ?_⟩⟩
  change X a ∉ (⊥ : Ideal (MvPolynomial (Fin 4) k))
  exact fun h => X_ne_zero a (Ideal.mem_bot.mp h)

/-- The hyperplane line bundle on the original projective space,
constructed from its four standard coordinate frames. -/
noncomputable def projectiveHyperplaneModuleSheaf (k : Type u) [Field k] :
    (Proj (homogeneousSubmodule (Fin 4) k)).Modules := by
  let : IsIntegral (Proj (homogeneousSubmodule (Fin 4) k)) := polynomialProjective_isIntegral k
  exact projectivePullbackHyperplaneModuleSheaf _ (𝟙 _) identity_projective_chart_nonempty

/-- The original coordinate section is the actual local frame of the
explicit hyperplane sheaf on its corresponding inverse chart. -/
theorem projective_pullback_hyperplane_regular_frame
    (Y : Scheme.{u}) [IsIntegral Y] (f : Y ⟶ P₃) (hU : ∀ a : Fin 4, Nonempty (f ⁻¹ᵁ U a))
    (a : Fin 4) : SchemeModuleRegularFrame (projectivePullbackHyperplaneModuleSheaf Y f hU) (f ⁻¹ᵁ U a) := by
  let V := fun i : Fin 4 => f ⁻¹ᵁ U i
  let w := projectivePullbackHyperplaneWeight Y f hU
  let t := projectivePullbackHyperplaneTransition Y f
  have hw := projectivePullbackHyperplaneWeight_ne_zero Y f hU
  have ht := projectivePullbackHyperplaneTransition_value Y f hU
  refine ⟨fun W hW => rationalFrameSheafLocalLinearEquiv Y V w hw t ht a hW, ?_⟩
  intro W W' j hW' r
  exact rationalFrameSheafLocalLinearEquiv_restrict Y V w hw t ht j a hW' r

theorem projective_hyperplane_regular_frame (a : Fin 4) :
    SchemeModuleRegularFrame (projectiveHyperplaneModuleSheaf k) (U a) := by
  let : IsIntegral (Proj (homogeneousSubmodule (Fin 4) k)) := polynomialProjective_isIntegral k
  have h := projective_pullback_hyperplane_regular_frame P₃ (𝟙 P₃) identity_projective_chart_nonempty a
  change SchemeModuleRegularFrame (projectiveHyperplaneModuleSheaf k) ((𝟙 P₃) ⁻¹ᵁ U a) at h
  have he : (𝟙 P₃) ⁻¹ᵁ U a = U a := by ext p; rfl
  rwa [he] at h

/-- The categorical pullback of the original hyperplane module agrees
on every inverse projective chart with its explicit original-coordinate
regular-frame sheaf. -/
noncomputable def projectiveHyperplaneCategoricalPullbackChartIso
    (Y : Scheme.{u}) [IsIntegral Y] (f : Y ⟶ P₃) (hU : ∀ a : Fin 4, Nonempty (f ⁻¹ᵁ U a))
    (a : Fin 4) :
    ((Scheme.Modules.pullback f).obj (projectiveHyperplaneModuleSheaf k)).restrict (f ⁻¹ᵁ U a).ι ≅
      (projectivePullbackHyperplaneModuleSheaf Y f hU).restrict (f ⁻¹ᵁ U a).ι :=
  (projective_hyperplane_regular_frame (k := k) a).pullbackRestrictIsoUnit f ≪≫
    (projective_pullback_hyperplane_regular_frame Y f hU a).restrictIsoUnit.symm

end DimensionFourDependence
