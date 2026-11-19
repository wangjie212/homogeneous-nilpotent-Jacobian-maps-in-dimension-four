import DimensionFourDependence.NormalizationCoordinateMorphism

/-! # Actual affine chart stalks preserve section germs

The global-stalk identification of an affine open immersion sends a
section germ to the localization of its actual affine coordinate value.
-/

namespace DimensionFourDependence

open AlgebraicGeometry CategoryTheory

universe u

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- A global section germ, expressed in an actual affine open chart,
has precisely its original coordinate value in the prime localization. -/
theorem schemeAffineOpenImmersionStalkIso_germ
    {X : Scheme.{u}} (B : CommRingCat.{u}) (j : Spec B ⟶ X) [IsOpenImmersion j]
    (q : PrimeSpectrum B) (U : X.Opens) (hU : ⊤ ≤ j ⁻¹ᵁ U) (r : Γ(X, U)) :
    schemeAffineOpenImmersionStalkIso B j q
      (X.presheaf.germ U (j q) (hU trivial) r) =
      algebraMap B (Localization.AtPrime q.asIdeal)
        ((Scheme.ΓSpecIso B).hom (j.appLE U ⊤ hU r)) := by
  change (Spec.stalkIso B q).hom
    (j.stalkMap q (X.presheaf.germ U (j q) (hU trivial) r)) = _
  rw [Scheme.Hom.germ_stalkMap_apply]
  calc
    _ = (Spec.stalkIso B q).hom
        ((Spec B).presheaf.germ ⊤ q trivial (j.appLE U ⊤ hU r)) := by
      congr 1
      exact ((Spec B).presheaf.germ_res_apply (homOfLE hU) q trivial (j.app U r)).symm
    _ = _ := ConcreteCategory.congr_hom (Spec.germ_stalkMapIso_hom q) _

/-- A morphism into an actual affine open, specified by a source-ring
map, induces exactly that same map on affine sections. -/
theorem affineSourceDiagram_appLE
    {X : Scheme.{u}} (B : CommRingCat.{u}) (U : X.affineOpens)
    (φ : Γ(X, U.1) ⟶ B) (f : Spec B ⟶ X)
    (hf : f = Spec.map φ ≫ U.2.fromSpec) (hU : ⊤ ≤ f ⁻¹ᵁ U.1) :
    f.appLE U.1 ⊤ hU ≫ (Scheme.ΓSpecIso B).hom = φ := by
  subst f
  rw [Scheme.Hom.comp_appLE, IsAffineOpen.fromSpec_app_self]
  simp only [Category.assoc, Scheme.Hom.map_appLE]
  change (Scheme.ΓSpecIso Γ(X, U.1)).inv ≫ (Spec.map φ).appTop ≫
    (Scheme.ΓSpecIso B).hom = φ
  rw [Scheme.ΓSpecIso_naturality, Iso.inv_hom_id_assoc]

/-- A morphism given by an affine source-ring map has its whole source
inside the specified actual affine target open. -/
theorem affineSourceDiagram_preimage_self
    {X : Scheme.{u}} (B : CommRingCat.{u}) (U : X.affineOpens)
    (φ : Γ(X, U.1) ⟶ B) (f : Spec B ⟶ X)
    (hf : f = Spec.map φ ≫ U.2.fromSpec) :
    f ⁻¹ᵁ U.1 = ⊤ := by
  rw [hf, Scheme.Hom.comp_preimage, IsAffineOpen.fromSpec_preimage_self]
  exact Scheme.Hom.preimage_top _

/-- Every affine coordinate prime maps to the original affine target
open in a specified affine source diagram. -/
theorem affineSourceDiagram_mem
    {X : Scheme.{u}} (B : CommRingCat.{u}) (U : X.affineOpens)
    (φ : Γ(X, U.1) ⟶ B) (f : Spec B ⟶ X)
    (hf : f = Spec.map φ ≫ U.2.fromSpec) (q : PrimeSpectrum B) :
    f q ∈ U.1 := by
  change q ∈ f ⁻¹ᵁ U.1
  rw [affineSourceDiagram_preimage_self B U φ f hf]
  trivial

/-- The actual pullback germ through a specified global scheme
morphism is its original affine-source value in the chart localization. -/
theorem schemeAffineOpenImmersionStalkIso_pullback_germ
    {X Y : Scheme.{u}} (B : CommRingCat.{u})
    (j : Spec B ⟶ Y) [IsOpenImmersion j] (f : Y ⟶ X) (U : X.affineOpens)
    (φ : Γ(X, U.1) ⟶ B)
    (hf : j ≫ f = Spec.map φ ≫ U.2.fromSpec)
    (q : PrimeSpectrum B) (r : Γ(X, U.1)) :
    schemeAffineOpenImmersionStalkIso B j q
      (Y.presheaf.germ (f ⁻¹ᵁ U.1) (j q)
        (affineSourceDiagram_mem B U φ (j ≫ f) hf q) (f.app U.1 r)) =
      algebraMap B (Localization.AtPrime q.asIdeal) (φ r) := by
  have htop : ⊤ ≤ j ⁻¹ᵁ f ⁻¹ᵁ U.1 := by
    rw [← Scheme.Hom.comp_preimage, affineSourceDiagram_preimage_self B U φ (j ≫ f) hf]
  rw [schemeAffineOpenImmersionStalkIso_germ B j q _ htop]
  have happ := affineSourceDiagram_appLE B U φ (j ≫ f) hf htop
  rw [Scheme.Hom.comp_appLE] at happ
  exact congrArg (algebraMap B (Localization.AtPrime q.asIdeal))
    (ConcreteCategory.congr_hom happ r)

end DimensionFourDependence
