import DimensionFourDependence.ProjectiveHyperplaneCategoricalFrames
import DimensionFourDependence.SchemeLineFramePullback
import DimensionFourDependence.ExtendedNormalizationHyperplaneSheaf

/-! # Categorical pullback of the original hyperplane line bundle -/

namespace DimensionFourDependence

open MvPolynomial AlgebraicGeometry CategoryTheory TopologicalSpace Opposite

attribute [local instance] MvPolynomial.gradedAlgebra

universe u
set_option maxHeartbeats 4200000
set_option synthInstance.maxHeartbeats 140000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

section Projective

variable {k : Type u} [Field k]
local notation "G" => homogeneousSubmodule (Fin 4) k
local notation "P₃" => Proj G
local notation "U" a:max => Proj.basicOpen G (X a)

private noncomputable def pullbackHyperplaneAtlas (Y : Scheme.{u}) [IsIntegral Y]
    (f : Y ⟶ P₃) (hU : ∀ a : Fin 4, Nonempty (f ⁻¹ᵁ U a)) :
    SchemeLineFrameAtlas (projectivePullbackHyperplaneModuleSheaf Y f hU)
      (fun a : Fin 4 => f ⁻¹ᵁ U a) := by
  let V := fun i : Fin 4 => f ⁻¹ᵁ U i
  let w := projectivePullbackHyperplaneWeight Y f hU
  let t := projectivePullbackHyperplaneTransition Y f
  have hw := projectivePullbackHyperplaneWeight_ne_zero Y f hU
  have ht := projectivePullbackHyperplaneTransition_value Y f hU
  refine
    { covers := f.iSup_preimage_eq_top (polynomialProjective_basicOpen_iSup k)
      frame := fun a _ hW => rationalFrameSheafLocalLinearEquiv Y V w hw t ht a hW
      restrict_frame := by
        intro a V' W' j hW r
        exact rationalFrameSheafLocalLinearEquiv_restrict Y V w hw t ht j a hW r
      transition := t
      transition_frame := ?_ }
  intro i j
  apply Subtype.ext
  funext p
  change w i * schemeRationalSectionFunction Y (V i ⊓ V j) 1 p =
    schemeRationalSectionFunction Y (V i ⊓ V j) (t i j) p *
      (w j * schemeRationalSectionFunction Y (V i ⊓ V j) 1 p)
  rw [ht, map_one, Pi.one_apply, mul_one, mul_one, div_mul_cancel₀ _ (hw j)]

private noncomputable def standardHyperplaneAtlas (k : Type u) [Field k] :
    SchemeLineFrameAtlas (projectiveHyperplaneModuleSheaf k)
      (fun a : Fin 4 => Proj.basicOpen (homogeneousSubmodule (Fin 4) k) (X a)) := by
  letI : IsIntegral (Proj (homogeneousSubmodule (Fin 4) k)) := polynomialProjective_isIntegral k
  exact pullbackHyperplaneAtlas _ (𝟙 _) identity_projective_chart_nonempty

private theorem hyperplaneTransition_pullback (Y : Scheme.{u}) [IsIntegral Y]
    (f : Y ⟶ P₃) (hU : ∀ a : Fin 4, Nonempty (f ⁻¹ᵁ U a)) (i j : Fin 4) :
    (pullbackHyperplaneAtlas Y f hU).transition i j =
      f.app (U i ⊓ U j) ((standardHyperplaneAtlas k).transition i j) := by
  let : IsIntegral P₃ := polynomialProjective_isIntegral k
  let r := projectiveCoordinateRatioSection k j i
  let ι : U i ⊓ U j ⟶ U j := Opens.infLERight (U i) (U j)
  change Y.presheaf.map (Opens.infLERight (f ⁻¹ᵁ U i) (f ⁻¹ᵁ U j)).op (f.app (U j) r) =
    f.app (U i ⊓ U j) ((P₃).presheaf.map ι.op ((𝟙 P₃ : P₃ ⟶ P₃).app (U j) r))
  rw [Scheme.Hom.id_app]
  change Y.presheaf.map (Opens.infLERight (f ⁻¹ᵁ U i) (f ⁻¹ᵁ U j)).op (f.app (U j) r) =
    f.app (U i ⊓ U j) ((P₃).presheaf.map ι.op r)
  exact (congrArg (fun g : Γ(P₃, U j) ⟶ Γ(Y, f ⁻¹ᵁ (U i ⊓ U j)) => g r)
    (f.naturality ι.op)).symm

/-- The hyperplane frame sheaf represents the actual categorical
pullback of the standard projective hyperplane line bundle. -/
noncomputable def projectiveHyperplaneCategoricalPullbackIso
    (Y : Scheme.{u}) [IsIntegral Y] (f : Y ⟶ P₃) (hU : ∀ a : Fin 4, Nonempty (f ⁻¹ᵁ U a)) :
    (Scheme.Modules.pullback f).obj (projectiveHyperplaneModuleSheaf k) ≅
      projectivePullbackHyperplaneModuleSheaf Y f hU :=
  schemeLineFramePullbackIso f (pullbackHyperplaneAtlas Y f hU) (standardHyperplaneAtlas k)
    (hyperplaneTransition_pullback Y f hU)

end Projective

section NormalizedPencil

variable {K : Type u} [Field K] [CharZero K]
  (H : Fin 4 → MvPolynomial (Fin 4) K) (I : ImageRelationWitness H)
  (E : Type u) [Field E] [Algebra (closedGaussParameterField H I) E]
  [Algebra.IsAlgebraic (closedGaussParameterField H I) E]
  {d : ℕ} (hH : IsHomogMap H d)
  (e : RatFunc K ≃ₐ[K] closedGaussParameterField H I)

local notation "N" => extendedClosedGaussNormalizationScheme H I E hH e
local notation "f" => extendedClosedGaussNormalizationProjectiveMap H I E hH e
local instance : IsIntegral N := extendedClosedGaussNormalizationScheme_isIntegral H I E hH e

/-- On the paper's normalized extended pencil the module sheaf used
for the section and multiplicity estimates is the categorical pullback
of the original hyperplane bundle. -/
noncomputable def extendedClosedGaussHyperplaneCategoricalPullbackIso :
    (Scheme.Modules.pullback f).obj (projectiveHyperplaneModuleSheaf E) ≅
      extendedClosedGaussNormalizationHyperplaneModuleSheaf H I E hH e := by
  refine projectiveHyperplaneCategoricalPullbackIso N f
    (extendedClosedGaussNormalizationProjectiveMap_chart_nonempty H I E hH e) ≪≫ eqToIso ?_
  change rationalFrameModuleSheaf N
      (fun a : Fin 4 => f ⁻¹ᵁ Proj.basicOpen (homogeneousSubmodule (Fin 4) E) (X a))
      (extendedClosedGaussNormalizationHyperplaneWeight H I E hH e) =
    rationalFrameModuleSheaf N
      (fun a : Fin 4 => extendedClosedGaussNormalizationChartOpen H I E hH e (finSuccEquiv' a))
      (extendedClosedGaussNormalizationHyperplaneWeight H I E hH e)
  rw [funext (extendedClosedGaussNormalizationProjectiveMap_preimage H I E hH e)]

end NormalizedPencil

end DimensionFourDependence
