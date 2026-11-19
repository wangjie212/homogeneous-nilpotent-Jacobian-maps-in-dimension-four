import DimensionFourDependence.QuinticBasicLiftCoordinates

/-! # Checking the direct polynomial expression for G in (6.43) -/

namespace DimensionFourDependence.Quintic

variable {R : Type*} [CommRing R]

def invariantFlowCoordinates (half η c t : R) (s : ActiveState R) : ActiveState R :=
  let U := coordinateU s.x s.y s.z t
  ⟨s.x + half * c * (-s.z * (U - s.z) + η * t ^ 2 * (1 + s.y)) +
      η * half ^ 2 * c ^ 2 * t ^ 3 * (U - 2 * s.z) + η ^ 2 * half ^ 3 * c ^ 3 * t ^ 6,
    s.y + half * c * t * (U - s.z) + η * half ^ 2 * c ^ 2 * t ^ 4,
    s.z - η * half * c * t ^ 3⟩

theorem invariantFlowCoordinates_auxiliary_image (half η c t : R) (s : ActiveState R)
    (hh : 2 * half = 1) :
    let b := quinticAuxiliaryState half s.x s.y s.z t
    let W := invariantFlowCoordinates half η c t s
    quinticAuxiliaryState half W.x W.y W.z t = auxiliaryT (η * t) (t ^ 2 * (half * c)) b := by
  let b := quinticAuxiliaryState half s.x s.y s.z t
  let q := half * c
  let h := t ^ 2 * q
  let a := η * t
  let w := vLiftCoordinateShift η t h s
  let κ := 2 * (b.v + a * h) * q - η * t ^ 3 * q ^ 2
  let U := coordinateU s.x s.y s.z t
  have hκ : κ = half * c * (U - s.z) + η * half ^ 2 * c ^ 2 * t ^ 3 := by
    change 2 * (half * (U - s.z) + a * h) * q - η * t ^ 3 * q ^ 2 = _
    dsimp only [a, h, q]
    linear_combination (half * c * (U - s.z)) * hh
  have hw : parameterShift t κ w = invariantFlowCoordinates half η c t s := by
    unfold parameterShift
    rw [hκ]
    dsimp only [w, h, q, vLiftCoordinateShift, invariantFlowCoordinates]
    congr 1 <;> ring
  have hv := quintic_basic_v_lift_coordinates half η t h s hh
  change quinticAuxiliaryState half w.x w.y w.z t = auxiliaryVShift (a * h) b at hv
  have hp := quintic_basic_p_lift_coordinates half t κ w
  dsimp only at hp
  rw [hw, hv] at hp
  have he : t ^ 2 * κ = 2 * (auxiliaryVShift (a * h) b).v * h - a * h ^ 2 := by
    dsimp only [κ, auxiliaryVShift, h, a]
    ring
  rw [he] at hp
  change quinticAuxiliaryState half (invariantFlowCoordinates half η c t s).x
    (invariantFlowCoordinates half η c t s).y (invariantFlowCoordinates half η c t s).z t =
      auxiliaryT a h b
  exact hp.trans (auxiliaryT_eq_auxiliary_shifts a h b).symm

end DimensionFourDependence.Quintic
