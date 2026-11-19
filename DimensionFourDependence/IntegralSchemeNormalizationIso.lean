import DimensionFourDependence.RelativeNormalizationIso
import DimensionFourDependence.IntegralSchemeFunctionFieldIso

/-! # Intrinsic normalization respects actual integral-scheme isomorphisms -/

namespace DimensionFourDependence

open AlgebraicGeometry CategoryTheory

universe u

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y] (e : X ≅ Y)

/-- Actual integral-scheme isomorphisms identify the intrinsic
normalizations in their respective actual function fields. -/
noncomputable def integralSchemeNormalizationIso :
    integralSchemeNormalization X ≅ integralSchemeNormalization Y := by
  let : QuasiCompact (integralSchemeGenericPointMorphism X) := integralSchemeGenericPointMorphism_quasiCompact X
  let : QuasiSeparated (integralSchemeGenericPointMorphism X) := integralSchemeGenericPointMorphism_quasiSeparated X
  let : QuasiCompact (integralSchemeGenericPointMorphism Y) := integralSchemeGenericPointMorphism_quasiCompact Y
  let : QuasiSeparated (integralSchemeGenericPointMorphism Y) := integralSchemeGenericPointMorphism_quasiSeparated Y
  exact relativeNormalizationArrowIso (integralSchemeGenericPointMorphism X) (integralSchemeGenericPointMorphism Y)
    (integralSchemeFunctionFieldSpectrumIso e) e (integralSchemeGenericPointMorphism_iso_naturality e)

/-- The intrinsic normalization isomorphism preserves the actual
integral normalization maps to the original schemes. -/
theorem integralSchemeNormalizationIso_map :
    (integralSchemeNormalizationIso e).hom ≫ integralSchemeNormalizationMap Y =
      integralSchemeNormalizationMap X ≫ e.hom := by
  let : QuasiCompact (integralSchemeGenericPointMorphism X) := integralSchemeGenericPointMorphism_quasiCompact X
  let : QuasiSeparated (integralSchemeGenericPointMorphism X) := integralSchemeGenericPointMorphism_quasiSeparated X
  let : QuasiCompact (integralSchemeGenericPointMorphism Y) := integralSchemeGenericPointMorphism_quasiCompact Y
  let : QuasiSeparated (integralSchemeGenericPointMorphism Y) := integralSchemeGenericPointMorphism_quasiSeparated Y
  exact relativeNormalizationArrowIso_fromNormalization
    (integralSchemeGenericPointMorphism X) (integralSchemeGenericPointMorphism Y)
    (integralSchemeFunctionFieldSpectrumIso e) e (integralSchemeGenericPointMorphism_iso_naturality e)

/-- The intrinsic normalization isomorphism also preserves the
actual function-field point factorization. -/
theorem integralSchemeNormalizationIso_genericPoint :
    integralSchemeNormalizationGenericPoint X ≫ (integralSchemeNormalizationIso e).hom =
      (integralSchemeFunctionFieldSpectrumIso e).hom ≫ integralSchemeNormalizationGenericPoint Y := by
  let : QuasiCompact (integralSchemeGenericPointMorphism X) := integralSchemeGenericPointMorphism_quasiCompact X
  let : QuasiSeparated (integralSchemeGenericPointMorphism X) := integralSchemeGenericPointMorphism_quasiSeparated X
  let : QuasiCompact (integralSchemeGenericPointMorphism Y) := integralSchemeGenericPointMorphism_quasiCompact Y
  let : QuasiSeparated (integralSchemeGenericPointMorphism Y) := integralSchemeGenericPointMorphism_quasiSeparated Y
  exact relativeNormalizationArrowIso_toNormalization
    (integralSchemeGenericPointMorphism X) (integralSchemeGenericPointMorphism Y)
    (integralSchemeFunctionFieldSpectrumIso e) e (integralSchemeGenericPointMorphism_iso_naturality e)

end DimensionFourDependence
