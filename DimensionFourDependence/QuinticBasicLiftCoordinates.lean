import DimensionFourDependence.QuinticGroupedAuxiliaryFactors
import DimensionFourDependence.QuinticFirstLiftAuxiliaryCoordinates

/-! # The polynomial coordinate formulas (6.23) and (6.24) -/

namespace DimensionFourDependence.Quintic

variable {R : Type*} [CommRing R]

theorem quintic_basic_p_lift_coordinates (half t κ : R) (s : ActiveState R) :
    let b := quinticAuxiliaryState half s.x s.y s.z t
    let w := parameterShift t κ s
    quinticAuxiliaryState half w.x w.y w.z t = auxiliaryPShift (t ^ 2 * κ) b := by
  let w := parameterShift t κ s
  have hu := coordinateU_invariant_under_parameterShift t κ s
  change coordinateU w.x w.y w.z t = coordinateU s.x s.y s.z t at hu
  have hz : w.z = s.z := rfl
  unfold quinticAuxiliaryState coordinateV coordinateW auxiliaryPShift
  change
    AuxiliaryState.mk (coordinateP w.y t) (half * (coordinateU w.x w.y w.z t - w.z))
      (half * (coordinateU w.x w.y w.z t + w.z)) =
    AuxiliaryState.mk (coordinateP s.y t + t ^ 2 * κ) (half * (coordinateU s.x s.y s.z t - s.z))
      (half * (coordinateU s.x s.y s.z t + s.z))
  rw [hu, hz]
  congr 1
  unfold w parameterShift coordinateP
  ring

def vLiftCoordinateShift (η t h : R) (s : ActiveState R) : ActiveState R :=
  ⟨s.x + η * (1 + s.y) * h, s.y, s.z - η * t * h⟩

theorem quintic_basic_v_lift_coordinates (half η t h : R) (s : ActiveState R)
    (hh : 2 * half = 1) :
    let b := quinticAuxiliaryState half s.x s.y s.z t
    let w := vLiftCoordinateShift η t h s
    quinticAuxiliaryState half w.x w.y w.z t = auxiliaryVShift (η * t * h) b := by
  let w := vLiftCoordinateShift η t h s
  let b := quinticAuxiliaryState half s.x s.y s.z t
  have hU : coordinateU w.x w.y w.z t = coordinateU s.x s.y s.z t + η * t * h := by
    unfold w coordinateU vLiftCoordinateShift
    ring
  have hy : w.y = s.y := rfl
  have hz : w.z = s.z - η * t * h := rfl
  change
    AuxiliaryState.mk (coordinateP w.y t) (half * (coordinateU w.x w.y w.z t - w.z))
      (half * (coordinateU w.x w.y w.z t + w.z)) =
    AuxiliaryState.mk (coordinateP s.y t) (half * (coordinateU s.x s.y s.z t - s.z) + η * t * h)
      (half * (coordinateU s.x s.y s.z t + s.z))
  rw [hU, hy, hz]
  congr 1
  · linear_combination (η * t * h) * hh
  · ring

end DimensionFourDependence.Quintic
