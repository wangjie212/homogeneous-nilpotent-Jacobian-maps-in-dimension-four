import DimensionFourDependence.IntegralSchemeNormalization

/-! # The actual field on inverse affine opens of the generic point

Every nonempty open of an integral scheme contains its generic point.
The inverse open in its function-field spectrum is therefore the whole
spectrum, and the induced map on sections is the original germ into the
actual function field. This identifies the affine normalization gluing
with integral closure in that same field.
-/

namespace DimensionFourDependence

open AlgebraicGeometry CategoryTheory TopologicalSpace Topology

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000

variable (X : Scheme.{u}) [IsIntegral X] (U : X.Opens) [Nonempty U]

/-- Every nonempty source open pulls back to the whole function-field spectrum. -/
theorem integralSchemeGenericPointMorphism_preimage_eq_top :
    integralSchemeGenericPointMorphism X ⁻¹ᵁ U = ⊤ := by
  have hx : genericPoint X ∈ U :=
    (show IsGenericPoint (genericPoint X) Set.univ from genericPoint_spec X).mem_open_set_iff U.isOpen
      |>.mpr (by simpa using (show Nonempty U from inferInstance))
  ext z
  change integralSchemeGenericPointMorphism X z ∈ U ↔ True
  have hz : z = IsLocalRing.closedPoint X.functionField :=
    Subsingleton.elim (α := PrimeSpectrum X.functionField) _ _
  rw [hz]
  change X.fromSpecStalk (genericPoint X) (IsLocalRing.closedPoint X.functionField) ∈ U ↔ True
  rw [Scheme.fromSpecStalk_closedPoint]
  exact iff_true_intro hx

/-- Sections on that actual inverse open are the original function field. -/
noncomputable def genericPointOpenSectionEquiv :
    Γ(Spec X.functionField, integralSchemeGenericPointMorphism X ⁻¹ᵁ U) ≃+* X.functionField :=
  ((Spec X.functionField).presheaf.mapIso
    (eqToIso (integralSchemeGenericPointMorphism_preimage_eq_top X U).symm).op ≪≫
      Scheme.ΓSpecIso X.functionField).commRingCatIsoToRingEquiv

/-- The affine gluing's coefficient map agrees with the actual source
germ under that field identification. -/
theorem genericPointOpenSectionEquiv_comp_app :
    (genericPointOpenSectionEquiv X U).toRingHom.comp
      ((integralSchemeGenericPointMorphism X).app U).hom = (X.germToFunctionField U).hom := by
  have hx : genericPoint X ∈ U :=
    (show IsGenericPoint (genericPoint X) Set.univ from genericPoint_spec X).mem_open_set_iff U.isOpen
      |>.mpr (by simpa using (show Nonempty U from inferInstance))
  let h := integralSchemeGenericPointMorphism_preimage_eq_top X U
  have hcancel :
      (Spec X.functionField).presheaf.map (homOfLE le_top).op ≫
        ((Spec X.functionField).presheaf.mapIso (eqToIso h.symm).op).hom = 𝟙 _ := by
    rw [Functor.mapIso_hom, ← Functor.map_comp]
    convert (Spec X.functionField).presheaf.map_id _ using 1
  change (((X.fromSpecStalk (genericPoint X)).app U ≫
    ((Spec X.functionField).presheaf.mapIso (eqToIso h.symm).op).hom ≫
      (Scheme.ΓSpecIso X.functionField).hom).hom) = _
  rw [Scheme.fromSpecStalk_app hx]
  have hcat : X.presheaf.germ U (genericPoint X) hx ≫
      (Scheme.ΓSpecIso X.functionField).inv ≫
      (Spec X.functionField).presheaf.map (homOfLE le_top).op ≫
      ((Spec X.functionField).presheaf.mapIso (eqToIso h.symm).op).hom ≫
      (Scheme.ΓSpecIso X.functionField).hom = X.presheaf.germ U (genericPoint X) hx := by
    rw [← Category.assoc _ _ (Scheme.ΓSpecIso X.functionField).hom, hcancel]
    simp
  exact congrArg CommRingCat.Hom.hom hcat

/-- On every nonempty affine open, the actual generic-point inverse-open
sections form the fraction field with the actual induced source action. -/
theorem generic_point_affine_open_sections_isFractionRing (hU : IsAffineOpen U) :
    letI := ((integralSchemeGenericPointMorphism X).app U).hom.toAlgebra
    IsFractionRing Γ(X, U)
      Γ(Spec X.functionField, integralSchemeGenericPointMorphism X ⁻¹ᵁ U) := by
  let : Algebra Γ(X, U)
      Γ(Spec X.functionField, integralSchemeGenericPointMorphism X ⁻¹ᵁ U) :=
    ((integralSchemeGenericPointMorphism X).app U).hom.toAlgebra
  let : IsFractionRing Γ(X, U) X.functionField := functionField_isFractionRing_of_isAffineOpen X U hU
  let e : Γ(Spec X.functionField, integralSchemeGenericPointMorphism X ⁻¹ᵁ U) ≃ₐ[Γ(X, U)]
      X.functionField :=
    { genericPointOpenSectionEquiv X U with
      commutes' := fun r => DFunLike.congr_fun (genericPointOpenSectionEquiv_comp_app X U) r }
  exact IsFractionRing.of_algEquiv e.symm

end DimensionFourDependence
