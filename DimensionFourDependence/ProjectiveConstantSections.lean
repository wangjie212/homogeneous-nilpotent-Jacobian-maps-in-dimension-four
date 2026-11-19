import DimensionFourDependence.PolynomialProjectiveBase
import DimensionFourDependence.ProjectivePullbackRationalCoordinates
import DimensionFourDependence.ExtendedGaussProjectiveSections

/-! # Original constants in actual projective sections and their generic pullbacks -/

namespace DimensionFourDependence

open MvPolynomial HomogeneousLocalization AlgebraicGeometry CategoryTheory TopologicalSpace

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (C : Type u) [Field C]

local notation "𝒢" => homogeneousSubmodule (Fin 4) C
local notation "P" => AlgebraicGeometry.Proj 𝒢

/-- Original coefficients in an actual homogeneous local ring, via
the degree-zero homogeneous fraction c/1. -/
noncomputable def projectiveConstantAtHom (p : ProjectiveSpectrum 𝒢) :
    C →+* HomogeneousLocalization 𝒢 p.asHomogeneousIdeal.toIdeal.primeCompl :=
  (HomogeneousLocalization.fromZeroRingHom 𝒢 p.asHomogeneousIdeal.toIdeal.primeCompl).comp
    (polynomialProjectiveDegreeZeroEquiv C).symm.toRingHom

/-- Original coefficients define actual regular projective sections
on every open, with their actual local-ring coefficient values. -/
noncomputable def projectiveConstantSectionHom (U : (P).Opens) : C →+* Γ(P, U) where
  toFun c := ⟨fun p => projectiveConstantAtHom C p.1 c, fun p =>
    ⟨U, p.2, 𝟙 _, 0, ⟨MvPolynomial.C c, isHomogeneous_C (Fin 4) c⟩, 1,
      (fun q => show (1 : MvPolynomial (Fin 4) C) ∈
        q.1.asHomogeneousIdeal.toIdeal.primeCompl from one_mem _), fun _ => rfl⟩⟩
  map_one' := by
    apply Subtype.ext
    funext p
    exact map_one (projectiveConstantAtHom C p.1)
  map_mul' c d := by
    apply Subtype.ext
    funext p
    exact map_mul (projectiveConstantAtHom C p.1) c d
  map_zero' := by
    apply Subtype.ext
    funext p
    exact map_zero (projectiveConstantAtHom C p.1)
  map_add' c d := by
    apply Subtype.ext
    funext p
    exact map_add (projectiveConstantAtHom C p.1) c d

/-- The actual constant section is exactly the canonical section of
its original degree-zero homogeneous fraction. -/
theorem projectiveConstantSectionHom_awayToSection (a : Fin 4) (c : C) :
    projectiveConstantSectionHom C (Proj.basicOpen 𝒢 (X a)) c =
      (Proj.basicOpenIsoAway 𝒢 (X a) (isHomogeneous_X (R := C) a) (by omega)).hom
        (Away.mk 𝒢 (isHomogeneous_X (R := C) a) 0 (MvPolynomial.C c)
          (isHomogeneous_C (Fin 4) c)) := by
  apply Subtype.ext
  funext p
  change projectiveConstantAtHom C p.1 c =
    HomogeneousLocalization.mapId 𝒢 (Submonoid.powers_le.mpr p.2)
      (Away.mk 𝒢 (isHomogeneous_X (R := C) a) 0 (MvPolynomial.C c)
        (isHomogeneous_C (Fin 4) c))
  apply HomogeneousLocalization.val_injective
  simp [projectiveConstantAtHom, polynomialProjectiveDegreeZeroEquiv,
    HomogeneousLocalization.fromZeroRingHom, Away.mk, HomogeneousLocalization.mapId,
    HomogeneousLocalization.map_mk, HomogeneousLocalization.val_mk]

/-- The actual geometric source-section evaluation preserves every
original field coefficient. -/
theorem projectiveConstantSectionHom_source_value
    {F : Type u} [Field F] [Algebra C F]
    (x : Fin 4 → F) (a : Fin 4) (ha : x a ≠ 0) (c : C) :
    projectiveAmbientSectionToSource x a ha
        (projectiveConstantSectionHom C (Proj.basicOpen 𝒢 (X a)) c) =
      algebraMap C (projectiveCoordinateChartAlgebra (C := C) x a) c := by
  rw [projectiveConstantSectionHom_awayToSection,
    projectiveAmbientSectionToSource_awayToSection]
  apply Subtype.ext
  change homogeneousCoordinateChartEval x a ha _ = algebraMap C F c
  rw [homogeneousCoordinateChartEval_mk]
  simp only [aeval_C, pow_zero, div_one]

variable (Y : Scheme.{u}) [IsIntegral Y]
  (f : Y ⟶ AlgebraicGeometry.Proj (homogeneousSubmodule (Fin 4) C))

/-- A single original-coefficient map into the source scheme's own
function field, given by its actual generic stalk map. -/
noncomputable def projectivePullbackScalarHom : C →+* Y.functionField :=
  (projectivePullbackGenericRatioHom Y f).comp
    (projectiveConstantAtHom C (f (genericPoint Y)))

/-- Generic pullback of an original constant on every nonempty
inverse projective open agrees with the one actual coefficient map. -/
theorem projectivePullbackScalarHom_chart
    (U : (P).Opens) [hU : Nonempty (f ⁻¹ᵁ U)] (c : C) :
    projectivePullbackScalarHom C Y f c =
      Y.germToFunctionField (f ⁻¹ᵁ U) (f.app U (projectiveConstantSectionHom C U c)) := by
  let hp : f (genericPoint Y) ∈ U :=
    ((genericPoint_spec Y).mem_open_set_iff (f ⁻¹ᵁ U).isOpen).mpr (by simpa using hU)
  have hstalk : (Proj.stalkIso' 𝒢 (f (genericPoint Y))).symm
      (projectiveConstantAtHom C (f (genericPoint Y)) c) =
      (P).presheaf.germ U (f (genericPoint Y)) hp (projectiveConstantSectionHom C U c) := by
    apply (Proj.stalkIso' 𝒢 (f (genericPoint Y))).injective
    rw [RingEquiv.apply_symm_apply]
    exact (Proj.stalkIso'_germ 𝒢 U (f (genericPoint Y)) hp
      (projectiveConstantSectionHom C U c)).symm
  exact (congrArg (fun z => f.stalkMap (genericPoint Y) z) hstalk).trans
    (Scheme.Hom.germ_stalkMap_apply f U (genericPoint Y) hp _)

end DimensionFourDependence
