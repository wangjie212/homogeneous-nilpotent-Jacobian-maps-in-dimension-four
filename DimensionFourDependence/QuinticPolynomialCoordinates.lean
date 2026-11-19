import DimensionFourDependence.BinaryPencilDeterminantIdentity

/-! # Polynomial identities for the rational coordinates in (6.16) -/

namespace DimensionFourDependence.Quintic

variable {R : Type*} [CommRing R]

def coordinateU (x y z t : R) : R := t * x + z * y

def coordinateP (y t : R) : R := t * y

def coordinateV (half x y z t : R) : R := half * (coordinateU x y z t - z)

def coordinateW (half x y z t : R) : R := half * (coordinateU x y z t + z)

theorem coordinateW_sub_coordinateV (half x y z t : R) (h : 2 * half = 1) :
    coordinateW half x y z t - coordinateV half x y z t = z := by
  calc
    _ = (2 * half) * z := by unfold coordinateW coordinateV; ring
    _ = _ := by rw [h, one_mul]

theorem coordinateW_add_coordinateV (half x y z t : R) (h : 2 * half = 1) :
    coordinateW half x y z t + coordinateV half x y z t = coordinateU x y z t := by
  calc
    _ = (2 * half) * coordinateU x y z t := by unfold coordinateW coordinateV; ring
    _ = _ := by rw [h, one_mul]

/-- The quadratic invariant in the auxiliary coordinates equals the
original invariant of the normalized quintic pencil. -/
theorem quintic_auxiliary_invariant_identity (half η x y z t : R) (h : 2 * half = 1) :
    η * t * coordinateP y t - coordinateV half x y z t ^ 2 +
      coordinateW half x y z t ^ 2 = z * t * x + (z ^ 2 + η * t ^ 2) * y := by
  let u := coordinateW half x y z t
  let v := coordinateV half x y z t
  change η * t * coordinateP y t - v ^ 2 + u ^ 2 = _
  calc
    _ = η * t * coordinateP y t + (u - v) * (u + v) := by ring
    _ = _ := by
      rw [coordinateW_sub_coordinateV half x y z t h, coordinateW_add_coordinateV half x y z t h]
      unfold coordinateP coordinateU
      ring

/-- Equality of the three auxiliary polynomials and the common fixed
coordinate determines the original coordinates over a domain. -/
theorem quintic_auxiliary_coordinates_injective [IsDomain R]
    (half t x y z x' y' z' : R) (hhalf : 2 * half = 1) (ht : t ≠ 0)
    (hp : coordinateP y t = coordinateP y' t)
    (hv : coordinateV half x y z t = coordinateV half x' y' z' t)
    (hu : coordinateW half x y z t = coordinateW half x' y' z' t) :
    x = x' ∧ y = y' ∧ z = z' := by
  have hz := congrArg₂ (· - ·) hu hv
  rw [coordinateW_sub_coordinateV _ _ _ _ _ hhalf,
    coordinateW_sub_coordinateV _ _ _ _ _ hhalf] at hz
  have hy : y = y' := mul_left_cancel₀ ht hp
  have hx := congrArg₂ (· + ·) hu hv
  rw [coordinateW_add_coordinateV _ _ _ _ _ hhalf,
    coordinateW_add_coordinateV _ _ _ _ _ hhalf] at hx
  unfold coordinateU at hx
  rw [hz, hy] at hx
  exact ⟨mul_left_cancel₀ ht (add_right_cancel hx), hy, hz⟩

end DimensionFourDependence.Quintic
