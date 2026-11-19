import DimensionFourDependence.NormalizationAffineCoordinateChart

/-! # The actual normalization coordinate charts commute with the global map

The coordinate-chart isomorphism is induced by the original affine
source map. Its inverse followed by the global normalization morphism
is exactly the spectrum morphism of that same source-ring inclusion.
-/

namespace DimensionFourDependence

open AlgebraicGeometry CategoryTheory

universe u

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (X : Scheme.{u}) [IsIntegral X] (U : X.affineOpens)

/-- The inverse of the actual affine normalization chart is the
original integral-closure chart inclusion used by the global gluing. -/
theorem integralSchemeNormalizationAffineChart_inv_ι :
    letI := ((integralSchemeGenericPointMorphism X).app U.1).hom.toAlgebra
    (integralSchemeNormalizationAffineChart X U).inv ≫
        (integralSchemeNormalizationMap X ⁻¹ᵁ U.1).ι =
      (integralSchemeGenericPointMorphism X).normalizationOpenCover.f U := by
  dsimp only [integralSchemeNormalizationAffineChart]
  exact IsOpenImmersion.isoOfRangeEq_inv_fac _ _ _

variable [Nonempty U.1] (B : Type u) [CommRing B] [IsDomain B]
  (e : Γ(X, U.1) ≃+* B)

/-- The actual normalized coordinate chart commutes with the global
normalization morphism through the specified original affine source map. -/
theorem integralSchemeNormalizationCoordinateChart_inv_to_base :
    (integralSchemeNormalizationCoordinateChart X U B e).inv ≫
        (integralSchemeNormalizationMap X ⁻¹ᵁ U.1).ι ≫
        integralSchemeNormalizationMap X =
      Spec.map (CommRingCat.ofHom
        ((algebraMap B (normalizationRing B)).comp e.toRingHom)) ≫ U.2.fromSpec := by
  let f := integralSchemeGenericPointMorphism X
  let T := Γ(Spec X.functionField, f ⁻¹ᵁ U.1)
  let : Algebra Γ(X, U.1) T := (f.app U.1).hom.toAlgebra
  let : IsFractionRing Γ(X, U.1) T :=
    generic_point_affine_open_sections_isFractionRing X U.1 U.2
  let b : integralClosure Γ(X, U.1) T ≃+* normalizationRing B :=
    normalizationCoordinateEquiv (T := T) e
  have hb : CommRingCat.ofHom (algebraMap Γ(X, U.1) (integralClosure Γ(X, U.1) T)) ≫
        CommRingCat.ofHom b.toRingHom =
      CommRingCat.ofHom ((algebraMap B (normalizationRing B)).comp e.toRingHom) := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro r
    exact normalizationCoordinateEquiv_algebraMap (T := T) e r
  change Spec.map (CommRingCat.ofHom b.toRingHom) ≫
    (integralSchemeNormalizationAffineChart X U).inv ≫
      (integralSchemeNormalizationMap X ⁻¹ᵁ U.1).ι ≫
      integralSchemeNormalizationMap X = _
  rw [← Category.assoc _ (integralSchemeNormalizationMap X ⁻¹ᵁ U.1).ι,
    integralSchemeNormalizationAffineChart_inv_ι]
  change Spec.map (CommRingCat.ofHom b.toRingHom) ≫
    f.normalizationOpenCover.f U ≫ f.fromNormalization = _
  rw [Scheme.Hom.ι_fromNormalization, ← Spec.map_comp_assoc]
  change Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U.1) (integralClosure Γ(X, U.1) T)) ≫
    CommRingCat.ofHom b.toRingHom) ≫ U.2.fromSpec = _
  rw [hb]

end DimensionFourDependence
