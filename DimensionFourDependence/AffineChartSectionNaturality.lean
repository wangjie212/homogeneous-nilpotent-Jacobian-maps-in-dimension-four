import DimensionFourDependence.AffineChartStalkNaturality

/-! # Affine chart section identifications are their actual geometric pullbacks -/

namespace DimensionFourDependence

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite

universe u

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {X : Scheme.{u}} (U : X.Opens) (B : CommRingCat.{u})
  (e : U.toScheme ≅ Spec B)

/-- The actual section identification determined by an affine open
chart isomorphism. -/
noncomputable def affineChartSectionEquiv : Γ(X, U) ≃+* B :=
  (U.topIso.symm ≪≫ (Scheme.Γ.mapIso e.op).symm ≪≫
    Scheme.ΓSpecIso B).commRingCatIsoToRingEquiv

/-- Pulling regular sections back along the actual chart inclusion
is exactly the section identification determined by the chart isomorphism. -/
theorem affineChartSectionEquiv_appLE
    (hU : ⊤ ≤ (e.inv ≫ U.ι) ⁻¹ᵁ U) (r : Γ(X, U)) :
    (Scheme.ΓSpecIso B).hom ((e.inv ≫ U.ι).appLE U ⊤ hU r) =
      affineChartSectionEquiv U B e r := by
  have h := Scheme.Hom.appLE_comp_appLE e.inv U.ι U ⊤ ⊤
    U.ι_preimage_self.ge (show ⊤ ≤ e.inv ⁻¹ᵁ ⊤ from le_rfl)
  have hι : U.ι.appLE U ⊤ U.ι_preimage_self.ge = U.topIso.inv := by
    rw [Scheme.Opens.ι_appLE]
    rfl
  rw [hι] at h
  have he : e.inv.appLE ⊤ ⊤ (show ⊤ ≤ e.inv ⁻¹ᵁ ⊤ from le_rfl) = e.inv.appTop := by
    simp [Scheme.Hom.appLE]
  rw [he] at h
  change (Scheme.ΓSpecIso B).hom ((e.inv ≫ U.ι).appLE U ⊤ hU r) =
    (Scheme.ΓSpecIso B).hom (e.inv.appTop (U.topIso.inv r))
  exact congrArg (fun k => (Scheme.ΓSpecIso B).hom (k r)) h.symm

/-- An actual affine-source diagram computes the coordinate value of
every section pulled back to the given affine chart. -/
theorem affineChartSectionEquiv_pullback {Y : Scheme.{u}} (f : X ⟶ Y)
    (V : Y.affineOpens) (φ : Γ(Y, V.1) ⟶ B)
    (hf : (e.inv ≫ U.ι) ≫ f = Spec.map φ ≫ V.2.fromSpec)
    (hUV : U ≤ f ⁻¹ᵁ V.1) (r : Γ(Y, V.1)) :
    affineChartSectionEquiv U B e (f.appLE V.1 U hUV r) = φ r := by
  let j := e.inv ≫ U.ι
  have hU : ⊤ ≤ j ⁻¹ᵁ U := by simp [j]
  have htop : ⊤ ≤ (j ≫ f) ⁻¹ᵁ V.1 :=
    hU.trans (j.preimage_mono hUV)
  have hcomp := Scheme.Hom.appLE_comp_appLE j f V.1 U ⊤ hUV hU
  have hφ := affineSourceDiagram_appLE B V φ (j ≫ f) hf htop
  calc
    _ = (Scheme.ΓSpecIso B).hom
        (j.appLE U ⊤ hU (f.appLE V.1 U hUV r)) :=
      (affineChartSectionEquiv_appLE U B e hU _).symm
    _ = (Scheme.ΓSpecIso B).hom ((j ≫ f).appLE V.1 ⊤ htop r) :=
      congrArg (fun k => (Scheme.ΓSpecIso B).hom (k r)) hcomp
    _ = φ r := ConcreteCategory.congr_hom hφ r

end DimensionFourDependence
