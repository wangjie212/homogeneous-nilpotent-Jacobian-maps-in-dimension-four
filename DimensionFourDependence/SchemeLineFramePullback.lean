import DimensionFourDependence.SchemeLineFrameAtlas
import Mathlib.CategoryTheory.Yoneda

/-! # The sheaf of pulled-back frames satisfies the pullback universal property -/

namespace DimensionFourDependence

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite

universe u v
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 140000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {X Y : Scheme.{u}} {ι : Type v} (f : X ⟶ Y)
  {U : ι → Y.Opens} {LX : X.Modules} {LY : Y.Modules}
  (FX : SchemeLineFrameAtlas LX (fun i => f ⁻¹ᵁ U i))
  (FY : SchemeLineFrameAtlas LY U)
  (ht : ∀ i j, FX.transition i j = f.app (U i ⊓ U j) (FY.transition i j))

include ht in
private theorem compatibleValues_pushforward_iff {M : X.Modules} (m : ∀ i, Γ(M, f ⁻¹ᵁ U i)) :
    FY.CompatibleValues (M := (Scheme.Modules.pushforward f).obj M) m ↔ FX.CompatibleValues m := by
  unfold SchemeLineFrameAtlas.CompatibleValues
  constructor <;> intro h i j
  · rw [ht]
    exact h i j
  · have hij := h i j
    rw [ht] at hij
    exact hij

private noncomputable def frameToPushforward : LY ⟶ (Scheme.Modules.pushforward f).obj LX :=
  FY.homOfCompatibleValues FX.generator
    ((compatibleValues_pushforward_iff f FX FY ht _).mpr FX.generator_compatible)

private theorem frameToPushforward_generator (i : ι) :
    (frameToPushforward f FX FY ht).app (U i) (FY.generator i) = FX.generator i :=
  FY.homOfCompatibleValues_generator _ _ i

private noncomputable def comparison : (Scheme.Modules.pullback f).obj LY ⟶ LX :=
  ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv LY LX).symm
    (frameToPushforward f FX FY ht)

private theorem comparison_equiv {M : X.Modules} (g : LX ⟶ M) :
    (Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv LY M (comparison f FX FY ht ≫ g) =
      frameToPushforward f FX FY ht ≫ (Scheme.Modules.pushforward f).map g := by
  rw [Adjunction.homEquiv_naturality_right, comparison, Equiv.apply_symm_apply]

private theorem composition_generator {M : X.Modules} (g : LX ⟶ M) (i : ι) :
    (frameToPushforward f FX FY ht ≫ (Scheme.Modules.pushforward f).map g).app (U i)
        (FY.generator i) = g.app (f ⁻¹ᵁ U i) (FX.generator i) := by
  rw [Scheme.Modules.Hom.comp_app, AddCommGrpCat.comp_apply, frameToPushforward_generator,
    Scheme.Modules.pushforward_map_app]
  rfl

private theorem comparison_isIso : IsIso (comparison f FX FY ht) := by
  apply isIso_of_coyoneda_map_bijective
  intro M
  let e := (Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv LY M
  constructor
  · intro g h hg
    apply FX.hom_ext_generator
    intro i
    have he := congrArg e hg
    change e (comparison f FX FY ht ≫ g) = e (comparison f FX FY ht ≫ h) at he
    rw [comparison_equiv, comparison_equiv] at he
    have he' := congrArg (fun q : LY ⟶ (Scheme.Modules.pushforward f).obj M =>
      q.app (U i) (FY.generator i)) he
    simpa only [composition_generator] using he'
  · intro q
    let m (i : ι) := (e q).app (U i) (FY.generator i)
    have hm : FX.CompatibleValues m := (compatibleValues_pushforward_iff f FX FY ht m).mp
      (FY.compatibleValues_of_hom (e q))
    refine ⟨FX.homOfCompatibleValues m hm, e.injective ?_⟩
    rw [comparison_equiv]
    apply FY.hom_ext_generator
    intro i
    rw [composition_generator, FX.homOfCompatibleValues_generator]

/-- If the transitions of a line bundle are pulled back on an inverse
chart cover, the resulting framed sheaf is the categorical pullback. -/
noncomputable def schemeLineFramePullbackIso : (Scheme.Modules.pullback f).obj LY ≅ LX :=
  letI := comparison_isIso f FX FY ht
  asIso (comparison f FX FY ht)

end DimensionFourDependence
