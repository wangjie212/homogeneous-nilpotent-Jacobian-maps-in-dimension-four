import DimensionFourDependence.QuinticSecondLiftAuxiliaryCoordinates

/-! # The triangular coordinate change for the first grouped lift -/

namespace DimensionFourDependence.Quintic

variable {R : Type*} [CommRing R]

def firstLiftFrame (half η t : R) (s : ActiveState R) : ActiveState R :=
  ⟨s.x - η * t * half * (s.y ^ 2 - s.y), s.y, s.z + η * t ^ 2 * half * s.y⟩

def firstLiftFrameInv (half η t : R) (s : ActiveState R) : ActiveState R :=
  ⟨s.x + η * t * half * (s.y ^ 2 - s.y), s.y, s.z - η * t ^ 2 * half * s.y⟩

theorem firstLiftFrameInv_frame (half η t : R) (s : ActiveState R) :
    firstLiftFrameInv half η t (firstLiftFrame half η t s) = s := by
  cases s
  unfold firstLiftFrameInv firstLiftFrame
  congr 1 <;> ring

theorem firstLiftFrame_frameInv (half η t : R) (s : ActiveState R) :
    firstLiftFrame half η t (firstLiftFrameInv half η t s) = s := by
  cases s
  unfold firstLiftFrameInv firstLiftFrame
  congr 1 <;> ring

theorem firstLiftFrame_coordinateU_sub_z (half η t : R) (s : ActiveState R) :
    let W := firstLiftFrame half η t s
    coordinateU W.x W.y W.z t - W.z = coordinateU s.x s.y s.z t - s.z := by
  unfold firstLiftFrame coordinateU
  ring

theorem firstLiftFrame_v_parameter (half η t : R) (s : ActiveState R) :
    let W := firstLiftFrame half η t s
    let b := quinticAuxiliaryState half s.x s.y s.z t
    b.v = half * (coordinateU W.x W.y W.z t - W.z) := by
  have hv := firstLiftFrame_coordinateU_sub_z half η t s
  dsimp only at hv ⊢
  rw [hv]
  rfl

theorem firstLiftFrame_r_parameter (half η t : R) (s : ActiveState R) (hh : 2 * half = 1) :
    let W := firstLiftFrame half η t s
    let b := quinticAuxiliaryState half s.x s.y s.z t
    b.u + half * auxiliaryq (η * t) b = W.z + b.v - half * b.v ^ 2 := by
  let b := quinticAuxiliaryState half s.x s.y s.z t
  have hu : b.u = b.v + s.z := quintic_auxiliary_u_eq_v_add_z half t s hh
  have hp : b.p = t * s.y := rfl
  change b.u + half * auxiliaryq (η * t) b = s.z + η * t ^ 2 * half * s.y + b.v - half * b.v ^ 2
  rw [hu, auxiliaryq, hp]
  ring

theorem coordinateU_invariant_under_parameterShift (t h : R) (s : ActiveState R) :
    let W := parameterShift t h s
    coordinateU W.x W.y W.z t = coordinateU s.x s.y s.z t := by
  unfold coordinateU parameterShift
  ring

/-- The transformed shear lifts the coordinates in (6.28), keeping the
parameter as a polynomial throughout the original ring. -/
theorem quintic_first_lift_auxiliary_coordinates (half η t f : R) (s : ActiveState R)
    (hh : 2 * half = 1) :
    let W := parameterShift t f (firstLiftFrame half η t s)
    let w := firstLiftFrameInv half η t W
    let b := quinticAuxiliaryState half s.x s.y s.z t
    quinticAuxiliaryState half w.x w.y w.z t =
      ⟨b.p + t ^ 2 * f, b.v, b.u - half * η * t ^ 3 * f⟩ := by
  let W₀ := firstLiftFrame half η t s
  let W := parameterShift t f W₀
  let w := firstLiftFrameInv half η t W
  let b := quinticAuxiliaryState half s.x s.y s.z t
  let a := quinticAuxiliaryState half w.x w.y w.z t
  have hw : firstLiftFrame half η t w = W := firstLiftFrame_frameInv half η t W
  have hV₀ : b.v = half * (coordinateU W₀.x W₀.y W₀.z t - W₀.z) :=
    firstLiftFrame_v_parameter half η t s
  have hV₁ : a.v = half * (coordinateU W.x W.y W.z t - W.z) := by
    have h := firstLiftFrame_v_parameter half η t w
    dsimp only at h
    rwa [hw] at h
  have hU : coordinateU W.x W.y W.z t = coordinateU W₀.x W₀.y W₀.z t :=
    coordinateU_invariant_under_parameterShift t f W₀
  have hz : W.z = W₀.z := rfl
  have hv : a.v = b.v := by rw [hV₁, hV₀, hU, hz]
  have hp : a.p = b.p + t ^ 2 * f := by
    change t * (s.y + t * f) = t * s.y + t ^ 2 * f
    ring
  have hza : w.z = s.z - half * η * t ^ 3 * f := by
    unfold w W W₀ parameterShift firstLiftFrameInv firstLiftFrame
    ring
  have hu : a.u = b.u - half * η * t ^ 3 * f := by
    have ha : a.u = a.v + w.z := quintic_auxiliary_u_eq_v_add_z half t w hh
    have hb : b.u = b.v + s.z := quintic_auxiliary_u_eq_v_add_z half t s hh
    rw [ha, hv, hza, hb]
    ring
  change a = ⟨b.p + t ^ 2 * f, b.v, b.u - half * η * t ^ 3 * f⟩
  rw [← hp, ← hv, ← hu]

end DimensionFourDependence.Quintic
