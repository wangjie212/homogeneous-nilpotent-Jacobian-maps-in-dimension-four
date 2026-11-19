import DimensionFourDependence.NormalizationAffineCoordinateChart

/-! # Affine coordinate isomorphisms retain their actual open inclusions

The section-ring isomorphism of an actual affine chart recovers that
same chart's scheme morphism, rather than an unrelated coordinate map.
-/

namespace DimensionFourDependence

open AlgebraicGeometry CategoryTheory

universe u

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The actual global sections of an affine open, in the coordinates
of a specified actual chart isomorphism. -/
noncomputable def affineOpenChartSectionEquiv
    {X : Scheme.{u}} (U : X.Opens) (B : CommRingCat.{u}) (i : U.toScheme ≅ Spec B) :
    Γ(X, U) ≃+* B :=
  (U.topIso.symm ≪≫ (Scheme.Γ.mapIso i.op).symm ≪≫ Scheme.ΓSpecIso B).commRingCatIsoToRingEquiv

/-- The coordinate map recovered from an actual affine chart section
isomorphism induces precisely that chart's original open inclusion. -/
theorem affineOpenChartSectionEquiv_to_base
    {X : Scheme.{u}} (U : X.Opens) (hU : IsAffineOpen U)
    (B : CommRingCat.{u}) (i : U.toScheme ≅ Spec B) :
    i.inv ≫ U.ι =
      Spec.map (CommRingCat.ofHom (affineOpenChartSectionEquiv U B i).toRingHom) ≫ hU.fromSpec := by
  have hi : i.inv ≫ U.toSpecΓ =
      Spec.map (CommRingCat.ofHom (affineOpenChartSectionEquiv U B i).toRingHom) := by
    dsimp only [Scheme.Opens.toSpecΓ]
    rw [← Category.assoc, Scheme.toSpecΓ_naturality, ← SpecMap_ΓSpecIso_hom,
      Category.assoc, ← Spec.map_comp, ← Spec.map_comp]
    rfl
  calc
    i.inv ≫ U.ι = i.inv ≫ U.toSpecΓ ≫ hU.fromSpec := by rw [IsAffineOpen.toSpecΓ_fromSpec]
    _ = _ := by rw [← Category.assoc, hi]

end DimensionFourDependence
