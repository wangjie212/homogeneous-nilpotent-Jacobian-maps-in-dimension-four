import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing

/-! # Compatible linear maps on subopens glue to a scheme-module morphism -/

namespace DimensionFourDependence

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite

universe u v
set_option maxHeartbeats 3400000
set_option synthInstance.maxHeartbeats 120000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {X : Scheme.{u}} {M N : X.Modules} {ι : Type v} (A : ι → X.Opens)

private def sectionCoverMap (W : X.Opens) (i : ι) : W ⊓ A i ⟶ W := homOfLE inf_le_left

private theorem sectionCover_covers (hA : iSup A = ⊤) (W : X.Opens) : W ≤ ⨆ i, W ⊓ A i := by
  intro x hx
  have h : x ∈ iSup A := by rw [hA]; trivial
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp h
  exact Opens.mem_iSup.mpr ⟨i, hx, hi⟩

/-- A sheaf module section is determined by its restrictions on the
intersection of its open with each member of a given cover. -/
theorem scheme_module_section_eq_of_cover (hA : iSup A = ⊤)
    (W : X.Opens) (s t : Γ(N, W))
    (h : ∀ i, N.presheaf.map (sectionCoverMap A W i).op s = N.presheaf.map (sectionCoverMap A W i).op t) :
    s = t :=
  (show TopCat.Sheaf Ab X from ⟨N.presheaf, N.isSheaf⟩).eq_of_locally_eq'
    (fun i => W ⊓ A i) W (sectionCoverMap A W) (sectionCover_covers A hA W) s t h

variable (hA : iSup A = ⊤)
  (f : ∀ (i : ι) (W : X.Opens), W ≤ A i → Γ(M, W) →ₗ[Γ(X, W)] Γ(N, W))
  (hf : ∀ (i : ι) {V W : X.Opens} (j : V ⟶ W) (hW : W ≤ A i) (s : Γ(M, W)),
    N.presheaf.map j.op (f i W hW s) = f i V (j.le.trans hW) (M.presheaf.map j.op s))
  (heq : ∀ (i j : ι) (W : X.Opens) (hi : W ≤ A i) (hj : W ≤ A j) (s : Γ(M, W)),
    f i W hi s = f j W hj s)

include hA hf heq in
private theorem scheme_module_localMaps_existsUnique (W : X.Opens) (s : Γ(M, W)) :
    ∃! t : Γ(N, W), ∀ i, N.presheaf.map (sectionCoverMap A W i).op t =
      f i (W ⊓ A i) inf_le_right (M.presheaf.map (sectionCoverMap A W i).op s) := by
  let B := fun i => W ⊓ A i
  let s₀ (i : ι) : Γ(N, B i) := f i (B i) inf_le_right (M.presheaf.map (sectionCoverMap A W i).op s)
  have hb : TopCat.Presheaf.IsCompatible N.presheaf B s₀ := by
    intro i j
    dsimp only [s₀]
    rw [hf i, hf j]
    have hmap : M.presheaf.map (Opens.infLELeft (B i) (B j)).op
          (M.presheaf.map (sectionCoverMap A W i).op s) =
        M.presheaf.map (Opens.infLERight (B i) (B j)).op
          (M.presheaf.map (sectionCoverMap A W j).op s) := by
      have he :
          (sectionCoverMap A W i).op ≫ (Opens.infLELeft (B i) (B j)).op =
            (sectionCoverMap A W j).op ≫ (Opens.infLERight (B i) (B j)).op :=
        Subsingleton.elim _ _
      rw [← AddCommGrpCat.comp_apply, ← AddCommGrpCat.comp_apply, ← Functor.map_comp,
        ← Functor.map_comp, he]
    rw [hmap]
    exact heq i j _ _ _ _
  exact (show TopCat.Sheaf Ab X from ⟨N.presheaf, N.isSheaf⟩).existsUnique_gluing'
    B W (sectionCoverMap A W) (sectionCover_covers A hA W) s₀ hb

private noncomputable def localMapsGluedSection (W : X.Opens) (s : Γ(M, W)) : Γ(N, W) :=
  (scheme_module_localMaps_existsUnique A hA f hf heq W s).choose

private theorem localMapsGluedSection_restrict_cover (W : X.Opens) (s : Γ(M, W)) (i : ι) :
    N.presheaf.map (sectionCoverMap A W i).op (localMapsGluedSection A hA f hf heq W s) =
      f i (W ⊓ A i) inf_le_right (M.presheaf.map (sectionCoverMap A W i).op s) :=
  (scheme_module_localMaps_existsUnique A hA f hf heq W s).choose_spec.1 i

private theorem localMapsGluedSection_restrict {V W : X.Opens} (j : V ⟶ W) (s : Γ(M, W)) :
    N.presheaf.map j.op (localMapsGluedSection A hA f hf heq W s) =
      localMapsGluedSection A hA f hf heq V (M.presheaf.map j.op s) := by
  apply scheme_module_section_eq_of_cover A hA V
  intro i
  let j' : V ⊓ A i ⟶ W ⊓ A i := homOfLE (inf_le_inf_right _ j.le)
  have hM : M.presheaf.map (sectionCoverMap A V i).op (M.presheaf.map j.op s) =
      M.presheaf.map j'.op (M.presheaf.map (sectionCoverMap A W i).op s) := by
    simp only [← ConcreteCategory.comp_apply, ← Functor.map_comp]
    rfl
  have hN (t : Γ(N, W)) : N.presheaf.map (sectionCoverMap A V i).op (N.presheaf.map j.op t) =
      N.presheaf.map j'.op (N.presheaf.map (sectionCoverMap A W i).op t) := by
    simp only [← ConcreteCategory.comp_apply, ← Functor.map_comp]
    rfl
  rw [localMapsGluedSection_restrict_cover, hM, hN, localMapsGluedSection_restrict_cover, hf i]

/-- The actual sheaf morphism induced by compatible restriction-natural
linear maps on the subopens of the cover. -/
noncomputable def schemeModuleHomOfLocalMaps : M ⟶ N :=
  ⟨PresheafOfModules.homMk
    { app W := AddCommGrpCat.ofHom
        { toFun := localMapsGluedSection A hA f hf heq W.unop
          map_zero' := by
            apply scheme_module_section_eq_of_cover A hA W.unop
            intro i
            rw [localMapsGluedSection_restrict_cover, map_zero, map_zero, map_zero]
          map_add' := by
            intro s t
            apply scheme_module_section_eq_of_cover A hA W.unop
            intro i
            simp only [localMapsGluedSection_restrict_cover, map_add] }
      naturality := by
        intro W V j
        apply ConcreteCategory.hom_ext
        intro s
        exact (localMapsGluedSection_restrict A hA f hf heq j.unop s).symm }
    (fun W r s => by
      change Γ(X, W.unop) at r
      change Γ(M, W.unop) at s
      apply scheme_module_section_eq_of_cover A hA W.unop
      intro i
      let j := sectionCoverMap A W.unop i
      change N.presheaf.map j.op (localMapsGluedSection A hA f hf heq W.unop (r • s)) =
        N.presheaf.map j.op (r • localMapsGluedSection A hA f hf heq W.unop s)
      dsimp only [j]
      rw [localMapsGluedSection_restrict_cover]
      change f i _ _ (M.presheaf.map j.op (r • s)) = N.presheaf.map j.op
        (r • localMapsGluedSection A hA f hf heq W.unop s)
      simp only [Scheme.Modules.map_smul, map_smul, localMapsGluedSection_restrict_cover, j])⟩

/-- On any subopen of a frame chart, the glued morphism is the original
specified local map with no change of its linear action. -/
theorem schemeModuleHomOfLocalMaps_app_of_le (i : ι) (W : X.Opens) (hW : W ≤ A i) (s : Γ(M, W)) :
    (schemeModuleHomOfLocalMaps A hA f hf heq).app W s = f i W hW s := by
  change localMapsGluedSection A hA f hf heq W s = _
  apply scheme_module_section_eq_of_cover A hA W
  intro j
  rw [localMapsGluedSection_restrict_cover, hf i]
  exact heq j i _ _ _ _

end DimensionFourDependence
