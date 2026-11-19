import DimensionFourDependence.QuinticCommutatorCoordinates

/-! # The polynomial flow used for the second grouped conjugate -/

namespace DimensionFourDependence.Quintic

structure ActiveState (R : Type*) where
  x : R
  y : R
  z : R

variable {R : Type*} [CommRing R]

def omega (half t : R) (s : ActiveState R) : R :=
  half * (t * s.x + (s.y - 1) * s.z) - 1

def secondInvariant (half t : R) (s : ActiveState R) : R := 2 * s.z - omega half t s ^ 2

def secondLiftFlow (half t h : R) (s : ActiveState R) : ActiveState R :=
  ⟨s.x + h * (2 + (1 - s.y) * omega half t s) + (1 - s.y) * t * half * h ^ 2,
    s.y, s.z + t * omega half t s * h + t ^ 2 * half * h ^ 2⟩

theorem secondLiftFlow_y (half t h : R) (s : ActiveState R) :
    (secondLiftFlow half t h s).y = s.y := rfl

theorem secondLiftFlow_omega (half t h : R) (s : ActiveState R) (hh : 2 * half = 1) :
    omega half t (secondLiftFlow half t h s) = omega half t s + t * h := by
  calc
    _ = omega half t s + (2 * half) * (t * h) := by unfold omega secondLiftFlow; ring
    _ = _ := by rw [hh, one_mul]

theorem secondLiftFlow_preserves_invariant (half t h : R) (s : ActiveState R) (hh : 2 * half = 1) :
    secondInvariant half t (secondLiftFlow half t h s) = secondInvariant half t s := by
  unfold secondInvariant
  rw [secondLiftFlow_omega half t h s hh]
  have hz : (secondLiftFlow half t h s).z =
      s.z + t * omega half t s * h + t ^ 2 * half * h ^ 2 := rfl
  rw [hz]
  linear_combination (t * h) ^ 2 * hh

theorem secondLiftFlow_add (half t h k : R) (s : ActiveState R) (hh : 2 * half = 1) :
    secondLiftFlow half t h (secondLiftFlow half t k s) = secondLiftFlow half t (h + k) s := by
  let w := secondLiftFlow half t k s
  change ⟨w.x + h * (2 + (1 - w.y) * omega half t w) + (1 - w.y) * t * half * h ^ 2,
    w.y, w.z + t * omega half t w * h + t ^ 2 * half * h ^ 2⟩ =
      secondLiftFlow half t (h + k) s
  have hω : omega half t w = omega half t s + t * k := secondLiftFlow_omega half t k s hh
  have hy : w.y = s.y := rfl
  rw [hω, hy]
  dsimp only [w, secondLiftFlow]
  congr 1
  · linear_combination -((1 - s.y) * t * h * k) * hh
  · linear_combination -(t ^ 2 * h * k) * hh

theorem secondLiftFlow_zero (half t : R) (s : ActiveState R) :
    secondLiftFlow half t 0 s = s := by
  cases s
  simp [secondLiftFlow]

end DimensionFourDependence.Quintic
