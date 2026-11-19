import DimensionFourDependence.QuinticSecondLiftFlow

/-! # The invariant shear and its parameter-shifting commutator -/

namespace DimensionFourDependence.Quintic

variable {R : Type*} [CommRing R]

def parameterShift (t k : R) (s : ActiveState R) : ActiveState R :=
  ⟨s.x - s.z * k, s.y + t * k, s.z⟩

theorem parameterShift_omega (half t k : R) (s : ActiveState R) :
    omega half t (parameterShift t k s) = omega half t s := by
  unfold omega parameterShift
  ring

theorem parameterShift_preserves_invariant (half t k : R) (s : ActiveState R) :
    secondInvariant half t (parameterShift t k s) = secondInvariant half t s := by
  unfold secondInvariant
  rw [parameterShift_omega]
  rfl

theorem parameterShift_inv (t k : R) (s : ActiveState R) :
    parameterShift t (-k) (parameterShift t k s) = s := by
  cases s
  unfold parameterShift
  congr 1 <;> ring

theorem parameterShift_commutes_secondLiftFlow (half t h k : R) (s : ActiveState R) :
    parameterShift t k (secondLiftFlow half t h s) =
      secondLiftFlow half t h (parameterShift t k s) := by
  conv_rhs => unfold secondLiftFlow
  rw [parameterShift_omega]
  unfold parameterShift secondLiftFlow
  congr 1 <;> ring

/-- Equation (6.39): the conjugation adds exactly the parameter
arising from the change of the y-coordinate by the invariant shear. -/
theorem secondLiftFlow_parameter_shifting_commutator
    (half t scale : R) (s : ActiveState R) (hh : 2 * half = 1) :
    let q := secondInvariant half t s
    let b := secondLiftFlow half t (-(scale * s.y)) s
    let c := parameterShift t q b
    parameterShift t (-q) (secondLiftFlow half t (scale * c.y) c) =
      secondLiftFlow half t (scale * t * q) s := by
  dsimp only
  let q := secondInvariant half t s
  let b := secondLiftFlow half t (-(scale * s.y)) s
  let c := parameterShift t q b
  change parameterShift t (-q) (secondLiftFlow half t (scale * c.y) c) =
    secondLiftFlow half t (scale * t * q) s
  have hc : c.y = s.y + t * q := rfl
  rw [hc, parameterShift_commutes_secondLiftFlow]
  have he : parameterShift t (-q) c = b := parameterShift_inv t q b
  rw [he]
  change secondLiftFlow half t (scale * (s.y + t * q))
    (secondLiftFlow half t (-(scale * s.y)) s) = secondLiftFlow half t (scale * t * q) s
  rw [secondLiftFlow_add _ _ _ _ _ hh]
  congr 1
  ring

end DimensionFourDependence.Quintic
