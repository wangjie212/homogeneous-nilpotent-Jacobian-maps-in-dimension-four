import DimensionFourDependence.RationalFrameLineBundle
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree

/-! # Categorical local frames and pullback of the rank-one unit -/

namespace DimensionFourDependence

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u
set_option maxHeartbeats 3300000
set_option synthInstance.maxHeartbeats 125000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem chart_inclusion_image_le {X : Scheme.{u}} (U : X.Opens) (V : U.toScheme.Opens) :
    U.ι ''ᵁ V ≤ U := (U.ι.image_mono le_top).trans_eq U.ι_image_top

/-- A sectionwise regular frame, natural in subopens, trivializes the
actual categorical restriction of the sheaf to that frame open. -/
noncomputable def SchemeModuleRegularFrame.restrictIsoUnit
    {X : Scheme.{u}} {M : X.Modules} {U : X.Opens} (h : SchemeModuleRegularFrame M U) :
    M.restrict U.ι ≅ SheafOfModules.unit U.toScheme.ringCatSheaf := by
  let e := h.choose
  have he := h.choose_spec
  have hlocal : Scheme.Modules.restrict (SheafOfModules.unit X.ringCatSheaf) U.ι ≅ M.restrict U.ι := by
    refine (Scheme.Modules.fullyFaithfulToPresheafOfModules (X := U.toScheme)).preimageIso
      (PresheafOfModules.isoMk (fun V => ?_) ?_)
    · let V' := U.ι ''ᵁ V.unop
      let f := e V' (chart_inclusion_image_le U V.unop)
      refine ModuleCat.isoMk f.toAddEquiv.toAddCommGrpIso ?_
      intro (r : Γ(U.toScheme, V.unop))
      ext (a : Γ(X, V'))
      change (U.ι.appIso V.unop).inv r • f a = f ((U.ι.appIso V.unop).inv r * a)
      exact (f.map_smul _ _).symm
    · intro V W j
      ext a
      let j' := U.ι.opensFunctor.map j.unop
      have ha := he _ _ j' (chart_inclusion_image_le U V.unop) a
      exact ha.symm
  exact hlocal.symm ≪≫ Scheme.Modules.restrictUnitIso U.ι

private theorem inverse_image_opens_final {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (Opens.map f.base).Final := by
  let F := Opens.map f.base
  have h₁ : (Functor.fromPUnit.{0} (⊤ : Y.Opens)).Final :=
    Functor.final_fromPUnit_of_isTerminal Limits.isTerminalTop
  have ht : F.obj (⊤ : Y.Opens) = ⊤ := Opens.map_top f.base
  have h₂ : (Functor.fromPUnit.{0} (F.obj (⊤ : Y.Opens))).Final := by
    rw [ht]
    exact Functor.final_fromPUnit_of_isTerminal Limits.isTerminalTop
  have h₃ : ((Functor.fromPUnit.{0} (⊤ : Y.Opens)) ⋙ F).Final :=
    Functor.final_of_natIso (F := Functor.fromPUnit.{0} (F.obj (⊤ : Y.Opens)))
      (Discrete.natIso (fun _ => Iso.refl _))
  exact Functor.final_of_final_comp (Functor.fromPUnit.{0} (⊤ : Y.Opens)) F

/-- The actual pullback functor sends the unit module sheaf to the unit
module sheaf, using the canonical adjoint of the structure-sheaf map. -/
noncomputable def schemePullbackUnitIso {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (Scheme.Modules.pullback f).obj (SheafOfModules.unit Y.ringCatSheaf) ≅ SheafOfModules.unit X.ringCatSheaf := by
  letI : (Opens.map f.base).Final := inverse_image_opens_final f
  letI : (SheafOfModules.pushforward.{u} f.toRingCatSheafHom).IsRightAdjoint :=
    (Scheme.Modules.pullbackPushforwardAdjunction f).isRightAdjoint
  let m := SheafOfModules.pullbackObjUnitToUnit (F := Opens.map f.base) f.toRingCatSheafHom
  letI : IsIso m := SheafOfModules.instIsIsoPullbackObjUnitToUnitOfFinal
    (F := Opens.map f.base) f.toRingCatSheafHom
  exact asIso m

/-- Restricting a categorical pullback to the inverse image of a regular
frame gives its actual local rank-one trivialization. -/
noncomputable def SchemeModuleRegularFrame.pullbackRestrictIsoUnit
    {X Y : Scheme.{u}} (f : X ⟶ Y) {M : Y.Modules} {U : Y.Opens}
    (h : SchemeModuleRegularFrame M U) :
    ((Scheme.Modules.pullback f).obj M).restrict (f ⁻¹ᵁ U).ι ≅
      SheafOfModules.unit (f ⁻¹ᵁ U).toScheme.ringCatSheaf := by
  let V := f ⁻¹ᵁ U
  let g := f ∣_ U
  have hg : g ≫ U.ι = V.ι ≫ f := morphismRestrict_ι f U
  exact (Scheme.Modules.restrictFunctorIsoPullback V.ι).app ((Scheme.Modules.pullback f).obj M) ≪≫
    (Scheme.Modules.pullbackComp V.ι f).app M ≪≫
    (Scheme.Modules.pullbackCongr hg.symm).app M ≪≫
    (Scheme.Modules.pullbackComp g U.ι).symm.app M ≪≫
    (Scheme.Modules.pullback g).mapIso ((Scheme.Modules.restrictFunctorIsoPullback U.ι).symm.app M) ≪≫
    (Scheme.Modules.pullback g).mapIso h.restrictIsoUnit ≪≫ schemePullbackUnitIso g

end DimensionFourDependence
