import DimensionFourDependence.GenericPointAffineField
import DimensionFourDependence.NormalizationRing

/-! # Normal local rings of the actual global normalization

At every point of the glued function-field normalization, an actual
affine integral-closure chart gives an integrally closed coordinate
domain. Its prime localization is the same scheme stalk, proving the
normality of the constructed global object at every point.
-/

namespace DimensionFourDependence

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000

variable (X : Scheme.{u}) [IsIntegral X]

/-- Every local ring of the actual glued normalization is integrally closed. -/
theorem integralSchemeNormalization_stalk_isIntegrallyClosed
    (y : integralSchemeNormalization X) :
    IsIntegrallyClosed ((integralSchemeNormalization X).presheaf.stalk y) := by
  let f := integralSchemeGenericPointMorphism X
  let n := f.fromNormalization
  let i := X.affineCover.idx (n y)
  let U : X.affineOpens :=
    ⟨(X.affineCover.f i).opensRange, isAffineOpen_opensRange (X.affineCover.f i)⟩
  have hyU : n y ∈ U.1 := X.affineCover.covers (n y)
  let : Nonempty U.1 := ⟨⟨n y, hyU⟩⟩
  let A := Γ(X, U.1)
  let T := Γ(Spec X.functionField, f ⁻¹ᵁ U.1)
  let : Algebra A T := (f.app U.1).hom.toAlgebra
  let et : T ≃+* X.functionField := genericPointOpenSectionEquiv X U.1
  let : Field T := (et.toMulEquiv.isField (Field.toIsField X.functionField)).toField
  let : IsFractionRing A T := generic_point_affine_open_sections_isFractionRing X U.1 U.2
  let B := integralClosure A T
  let : IsIntegrallyClosed B := integralClosure.isIntegrallyClosedOfFiniteExtension T
  let j : Spec (CommRingCat.of B) ⟶ f.normalization := f.normalizationOpenCover.f U
  have hy : y ∈ j.opensRange :=
    (f.fromNormalization_preimage U).le hyU
  obtain ⟨z, hz⟩ := hy
  let : Algebra B ((Spec (CommRingCat.of B)).presheaf.stalk z) :=
    (StructureSheaf.toStalk (CommRingCat.of B) z).hom.toAlgebra
  let : IsLocalization.AtPrime ((Spec (CommRingCat.of B)).presheaf.stalk z) z.asIdeal :=
    StructureSheaf.IsLocalization.to_stalk (CommRingCat.of B) z
  have hzclosed : IsIntegrallyClosed ((Spec (CommRingCat.of B)).presheaf.stalk z) := by
    exact isIntegrallyClosed_of_isLocalization (R := B)
      ((Spec (CommRingCat.of B)).presheaf.stalk z) z.asIdeal.primeCompl
      z.asIdeal.primeCompl_le_nonZeroDivisors
  let : IsIntegrallyClosed ((Spec (CommRingCat.of B)).presheaf.stalk z) := hzclosed
  have htarget : IsIntegrallyClosed (f.normalization.presheaf.stalk (j z)) :=
    IsIntegrallyClosed.of_equiv (asIso (j.stalkMap z)).commRingCatIsoToRingEquiv.symm
  exact hz ▸ htarget

end DimensionFourDependence
