import DimensionFourDependence.SheafModuleLocalMorphisms

/-! # Maps from a line bundle are determined by compatible frame values -/

namespace DimensionFourDependence

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite

universe u v
set_option maxHeartbeats 5000000
set_option synthInstance.maxHeartbeats 140000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {X : Scheme.{u}} {ι : Type v}

/-- A choice of actual linear frames on a cover, including their
restriction maps and their scalar transition on each overlap. -/
structure SchemeLineFrameAtlas (L : X.Modules) (A : ι → X.Opens) where
  covers : iSup A = ⊤
  frame : ∀ (i : ι) (W : X.Opens), W ≤ A i → Γ(X, W) ≃ₗ[Γ(X, W)] Γ(L, W)
  restrict_frame : ∀ (i : ι) {V W : X.Opens} (j : V ⟶ W) (hW : W ≤ A i) (r : Γ(X, W)),
    L.presheaf.map j.op (frame i W hW r) = frame i V (j.le.trans hW) (X.presheaf.map j.op r)
  transition : ∀ i j : ι, Γ(X, A i ⊓ A j)
  transition_frame : ∀ i j : ι,
    frame i (A i ⊓ A j) inf_le_left 1 = transition i j • frame j (A i ⊓ A j) inf_le_right 1

variable {L M : X.Modules} {A : ι → X.Opens} (F : SchemeLineFrameAtlas L A)

/-- The actual generator on a frame chart. -/
noncomputable def SchemeLineFrameAtlas.generator (i : ι) : Γ(L, A i) := F.frame i _ le_rfl 1

theorem SchemeLineFrameAtlas.restrict_generator (i : ι) {W : X.Opens} (hW : W ≤ A i) :
    L.presheaf.map (homOfLE hW).op (F.generator i) = F.frame i W hW 1 := by
  rw [generator, F.restrict_frame, map_one]

private theorem SchemeLineFrameAtlas.frame_apply_eq_smul (i : ι) {W : X.Opens} (hW : W ≤ A i) (r : Γ(X, W)) :
    F.frame i W hW r = r • F.frame i W hW 1 := by
  simpa only [smul_eq_mul, mul_one] using (F.frame i W hW).map_smul r 1

private theorem SchemeLineFrameAtlas.inverse_frame_restrict (i : ι) {V W : X.Opens} (j : V ⟶ W) (hW : W ≤ A i)
    (s : Γ(L, W)) :
    (F.frame i V (j.le.trans hW)).symm (L.presheaf.map j.op s) =
      X.presheaf.map j.op ((F.frame i W hW).symm s) := by
  apply (F.frame i V (j.le.trans hW)).injective
  rw [LinearEquiv.apply_symm_apply, ← F.restrict_frame i j hW, LinearEquiv.apply_symm_apply]

/-- A proposed family of images of the atlas generators respects all
their actual overlap transitions. -/
def SchemeLineFrameAtlas.CompatibleValues (m : ∀ i : ι, Γ(M, A i)) : Prop := ∀ i j : ι,
  M.presheaf.map (Opens.infLELeft (A i) (A j)).op (m i) =
    F.transition i j • M.presheaf.map (Opens.infLERight (A i) (A j)).op (m j)

private theorem app_restrict (g : L ⟶ M) {V W : X.Opens} (j : V ⟶ W) (s : Γ(L, W)) :
    g.app V (L.presheaf.map j.op s) = M.presheaf.map j.op (g.app W s) :=
  congrArg (fun a : Γ(L, W) ⟶ Γ(M, V) => a s) (g.mapPresheaf.naturality j.op)

theorem SchemeLineFrameAtlas.compatibleValues_of_hom (g : L ⟶ M) :
    F.CompatibleValues (fun i => g.app (A i) (F.generator i)) := by
  intro i j
  change M.presheaf.map (homOfLE inf_le_left : A i ⊓ A j ⟶ A i).op
      (g.app (A i) (F.generator i)) =
    F.transition i j • M.presheaf.map (homOfLE inf_le_right : A i ⊓ A j ⟶ A j).op
      (g.app (A j) (F.generator j))
  rw [← app_restrict, ← app_restrict, F.restrict_generator i, F.restrict_generator j,
    F.transition_frame, Scheme.Modules.Hom.app_smul]

theorem SchemeLineFrameAtlas.generator_compatible : F.CompatibleValues F.generator := by
  intro i j
  exact (F.restrict_generator i inf_le_left).trans
    ((F.transition_frame i j).trans (congrArg (F.transition i j • ·)
      (F.restrict_generator j inf_le_right).symm))

private noncomputable def SchemeLineFrameAtlas.morphismOnChart (m : ∀ i : ι, Γ(M, A i))
    (i : ι) (W : X.Opens) (hW : W ≤ A i) : Γ(L, W) →ₗ[Γ(X, W)] Γ(M, W) :=
  (LinearMap.toSpanSingleton _ _ (M.presheaf.map (homOfLE hW).op (m i))).comp
    (F.frame i W hW).symm.toLinearMap

private theorem SchemeLineFrameAtlas.morphismOnChart_restrict (m : ∀ i : ι, Γ(M, A i)) (i : ι)
    {V W : X.Opens} (j : V ⟶ W) (hW : W ≤ A i) (s : Γ(L, W)) :
    M.presheaf.map j.op (F.morphismOnChart m i W hW s) =
      F.morphismOnChart m i V (j.le.trans hW) (L.presheaf.map j.op s) := by
  change M.presheaf.map j.op ((F.frame i W hW).symm s • M.presheaf.map (homOfLE hW).op (m i)) =
    (F.frame i V (j.le.trans hW)).symm (L.presheaf.map j.op s) •
      M.presheaf.map (homOfLE (j.le.trans hW)).op (m i)
  rw [Scheme.Modules.map_smul, F.inverse_frame_restrict, ← AddCommGrpCat.comp_apply,
    ← Functor.map_comp]
  rfl

private theorem SchemeLineFrameAtlas.restrict_overlap_value (m : ∀ i : ι, Γ(M, A i)) (hm : F.CompatibleValues m)
    (i j : ι) (W : X.Opens) (hi : W ≤ A i) (hj : W ≤ A j) :
    M.presheaf.map (homOfLE hi).op (m i) =
      X.presheaf.map (homOfLE (le_inf hi hj)).op (F.transition i j) • M.presheaf.map (homOfLE hj).op (m j) := by
  have h := congrArg (fun r => M.presheaf.map (homOfLE (le_inf hi hj)).op r) (hm i j)
  rw [Scheme.Modules.map_smul] at h
  rw [← AddCommGrpCat.comp_apply, ← AddCommGrpCat.comp_apply, ← Functor.map_comp, ← Functor.map_comp] at h
  exact h

private theorem SchemeLineFrameAtlas.restrict_overlap_frame (i j : ι) (W : X.Opens) (hi : W ≤ A i) (hj : W ≤ A j) :
    F.frame i W hi 1 = X.presheaf.map (homOfLE (le_inf hi hj)).op (F.transition i j) • F.frame j W hj 1 := by
  have h := F.restrict_overlap_value F.generator F.generator_compatible i j W hi hj
  simpa only [F.restrict_generator] using h

private theorem SchemeLineFrameAtlas.morphismOnChart_overlap (m : ∀ i : ι, Γ(M, A i)) (hm : F.CompatibleValues m)
    (i j : ι) (W : X.Opens) (hi : W ≤ A i) (hj : W ≤ A j) (s : Γ(L, W)) :
    F.morphismOnChart m i W hi s = F.morphismOnChart m j W hj s := by
  let r := (F.frame i W hi).symm s
  let t := X.presheaf.map (homOfLE (le_inf hi hj)).op (F.transition i j)
  have he : (F.frame j W hj).symm s = r * t := by
    apply (F.frame j W hj).injective
    rw [LinearEquiv.apply_symm_apply, F.frame_apply_eq_smul j hj (r * t), mul_smul,
      ← F.restrict_overlap_frame i j W hi hj, ← F.frame_apply_eq_smul i hi r]
    exact ((F.frame i W hi).apply_symm_apply s).symm
  change r • M.presheaf.map (homOfLE hi).op (m i) =
    (F.frame j W hj).symm s • M.presheaf.map (homOfLE hj).op (m j)
  rw [F.restrict_overlap_value m hm i j W hi hj, he, mul_smul]

/-- A compatible family of generator values defines an actual global
morphism of module sheaves. -/
noncomputable def SchemeLineFrameAtlas.homOfCompatibleValues
    (m : ∀ i : ι, Γ(M, A i)) (hm : F.CompatibleValues m) : L ⟶ M :=
  schemeModuleHomOfLocalMaps A F.covers (F.morphismOnChart m)
    (F.morphismOnChart_restrict m) (F.morphismOnChart_overlap m hm)

theorem SchemeLineFrameAtlas.homOfCompatibleValues_generator (m : ∀ i : ι, Γ(M, A i)) (hm : F.CompatibleValues m) (i : ι) :
    (F.homOfCompatibleValues m hm).app (A i) (F.generator i) = m i := by
  rw [homOfCompatibleValues, schemeModuleHomOfLocalMaps_app_of_le _ _ _ _ _ i (A i) le_rfl]
  change (F.frame i (A i) le_rfl).symm (F.frame i (A i) le_rfl 1) •
    M.presheaf.map (homOfLE (le_rfl : A i ≤ A i)).op (m i) = m i
  rw [LinearEquiv.symm_apply_apply, one_smul]
  change M.presheaf.map (𝟙 (op (A i))) (m i) = m i
  rw [M.presheaf.map_id]
  rfl

/-- Two actual morphisms agreeing on all frame generators agree everywhere. -/
theorem SchemeLineFrameAtlas.hom_ext_generator (g h : L ⟶ M)
    (he : ∀ i, g.app (A i) (F.generator i) = h.app (A i) (F.generator i)) : g = h := by
  apply Scheme.Modules.hom_ext
  intro W
  ext s
  apply scheme_module_section_eq_of_cover A F.covers W
  intro i
  let V := W ⊓ A i
  let j : V ⟶ W := homOfLE inf_le_left
  let j' : V ⟶ A i := homOfLE inf_le_right
  let v := L.presheaf.map j.op s
  let r := (F.frame i V inf_le_right).symm v
  have hv : v = r • L.presheaf.map j'.op (F.generator i) := by
    rw [show L.presheaf.map j'.op (F.generator i) = F.frame i V inf_le_right 1 from F.restrict_generator i _]
    rw [← F.frame_apply_eq_smul, LinearEquiv.apply_symm_apply]
  change M.presheaf.map j.op (g.app W s) = M.presheaf.map j.op (h.app W s)
  have hg : g.app V v = _ := app_restrict g j s
  have hh : h.app V v = _ := app_restrict h j s
  rw [← hg, ← hh, hv, Scheme.Modules.Hom.app_smul, Scheme.Modules.Hom.app_smul]
  have hg' := app_restrict g j' (F.generator i)
  have hh' := app_restrict h j' (F.generator i)
  rw [hg', hh']
  exact congrArg (fun s => r • M.presheaf.map j'.op s) (he i)

end DimensionFourDependence
