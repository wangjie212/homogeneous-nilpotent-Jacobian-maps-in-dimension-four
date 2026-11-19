import DimensionFourDependence.NormalizationCoordinateEquiv
import DimensionFourDependence.GenericPointAffineField

/-! # The global normalization's actual affine coordinate normalizations

An explicit coordinate isomorphism on an original affine open induces
an actual scheme isomorphism from its inverse open in the global
normalization to the canonical normalization of that coordinate ring.
-/

namespace DimensionFourDependence

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The inverse affine open of the actual global function-field normalization
is the canonical normalization of its explicitly identified coordinate ring. -/
noncomputable def integralSchemeNormalizationCoordinateChart
    (X : Scheme.{u}) [IsIntegral X] (U : X.affineOpens) [Nonempty U.1]
    (B : Type u) [CommRing B] [IsDomain B] (e : Γ(X, U.1) ≃+* B) :
    (integralSchemeNormalizationMap X ⁻¹ᵁ U.1).toScheme ≅
      Spec (CommRingCat.of (normalizationRing B)) := by
  let T := Γ(Spec X.functionField, integralSchemeGenericPointMorphism X ⁻¹ᵁ U.1)
  let : Algebra Γ(X, U.1) T := ((integralSchemeGenericPointMorphism X).app U.1).hom.toAlgebra
  let : IsFractionRing Γ(X, U.1) T := generic_point_affine_open_sections_isFractionRing X U.1 U.2
  exact integralSchemeNormalizationAffineChart X U ≪≫
    Scheme.Spec.mapIso (normalizationCoordinateEquiv (T := T) e).symm.toCommRingCatIso.op

/-- An actual affine open immersion identifies a global scheme stalk
with the original coordinate prime localization. -/
noncomputable def schemeAffineOpenImmersionStalkIso
    {X : Scheme.{u}} (B : CommRingCat.{u}) (j : Spec B ⟶ X) [IsOpenImmersion j]
    (q : PrimeSpectrum B) :
    X.presheaf.stalk (j q) ≃+* Localization.AtPrime q.asIdeal :=
  ((asIso (j.stalkMap q)) ≪≫ Spec.stalkIso B q).commRingCatIsoToRingEquiv

end DimensionFourDependence
