import DimensionFourDependence.ProjectiveCoordinateRatioSections
import DimensionFourDependence.ExtendedGaussProjectiveSections

/-! # Actual original coordinate sections retain their original ratio evaluations -/

namespace DimensionFourDependence

open MvPolynomial HomogeneousLocalization AlgebraicGeometry CategoryTheory

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {C F : Type u} [Field C] [Field F] [Algebra C F]

local notation "𝒢" => homogeneousSubmodule (Fin 4) C

/-- The actual regular coordinate-ratio section is precisely the
canonical Proj chart section of its original homogeneous fraction. -/
theorem projectiveCoordinateRatioSection_awayToSection (a i : Fin 4) :
    projectiveCoordinateRatioSection C a i =
      (Proj.basicOpenIsoAway 𝒢 (X a) (isHomogeneous_X (R := C) a) (by omega)).hom
        (Away.mk 𝒢 (isHomogeneous_X (R := C) a) 1 (X i)
          (by simpa using isHomogeneous_X (R := C) i)) := by
  apply Subtype.ext
  funext p
  change projectiveCoordinateRatioAt C p.1 a i p.2 =
    HomogeneousLocalization.mapId 𝒢 (Submonoid.powers_le.mpr p.2)
      (Away.mk 𝒢 (isHomogeneous_X (R := C) a) 1 (X i)
        (by simpa using isHomogeneous_X (R := C) i))
  simp [projectiveCoordinateRatioAt, Away.mk, HomogeneousLocalization.mapId,
    HomogeneousLocalization.map_mk]

/-- Evaluating the actual coordinate section in an original source
chart returns its exact original homogeneous coordinate ratio. -/
theorem projectiveCoordinateRatioSection_source_value
    (x : Fin 4 → F) (a : Fin 4) (ha : x a ≠ 0) (i : Fin 4) :
    (projectiveAmbientSectionToSource x a ha
      (projectiveCoordinateRatioSection C a i) : F) = x i / x a := by
  rw [projectiveCoordinateRatioSection_awayToSection,
    projectiveAmbientSectionToSource_awayToSection]
  change homogeneousCoordinateChartEval x a ha _ = _
  rw [homogeneousCoordinateChartEval_mk]
  simp only [aeval_X, pow_one]

/-- The actual coordinate-ratio section is the original ratio-chart
generator under the entire geometric source-section identification. -/
theorem projectiveCoordinateRatioSection_source_transition
    (x : Fin 4 → F) (a : Fin 4) (ha : x a ≠ 0) (i : Fin 4) :
    projectiveAmbientSectionToSource x a ha (projectiveCoordinateRatioSection C a i) =
      projectiveChartTransition (C := C) x a i := by
  apply Subtype.ext
  exact projectiveCoordinateRatioSection_source_value x a ha i

end DimensionFourDependence
