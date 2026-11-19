import DimensionFourDependence.QuinticInvariantFlowSign

/-! # The commutator computes the original normalized quintic coordinates -/

namespace DimensionFourDependence.Quintic

variable {R : Type*} [CommRing R]

def quinticAuxiliaryState (half x y z t : R) : AuxiliaryState R :=
  ⟨coordinateP y t, coordinateV half x y z t, coordinateW half x y z t⟩

def quinticInvariant (η x y z t : R) : R := z * t * x + (z ^ 2 + η * t ^ 2) * y

theorem quinticAuxiliaryState_Q (half η x y z t : R) (hhalf : 2 * half = 1) :
    auxiliaryQ (η * t) (quinticAuxiliaryState half x y z t) = quinticInvariant η x y z t :=
  quintic_auxiliary_invariant_identity half η x y z t hhalf

theorem quinticAuxiliaryState_involution (half x y z t : R) :
    quinticAuxiliaryState half x (-y) (-z) t =
      auxiliaryInvolution (quinticAuxiliaryState half x y z t) := by
  unfold quinticAuxiliaryState auxiliaryInvolution coordinateP coordinateV coordinateW coordinateU
  congr 1 <;> ring

/-- Equations (6.20)–(6.21) as identities of polynomial coordinates.
The common fourth coordinate is fixed throughout. -/
theorem quintic_shear_auxiliary_commutator
    (half η scale x y z t : R) (hhalf : 2 * half = 1) :
    let S := quinticInvariant η x y z t
    let x' := x + scale * (z ^ 2 + η * t ^ 2) * S
    let y' := y - scale * (z * t) * S
    let s := quinticAuxiliaryState half x y z t
    let a := η * t
    let c := half * (scale * t ^ 2)
    quinticAuxiliaryState half x' y' z t =
      auxiliaryInvariantT a c (auxiliaryInvolution (auxiliaryInvariantT a (-c)
        (auxiliaryInvolution s))) := by
  let S := quinticInvariant η x y z t
  let x' := x + scale * (z ^ 2 + η * t ^ 2) * S
  let y' := y - scale * (z * t) * S
  let s := quinticAuxiliaryState half x y z t
  let c := half * (scale * t ^ 2)
  let a := η * t
  change quinticAuxiliaryState half x' y' z t =
    auxiliaryInvariantT a c (auxiliaryInvolution (auxiliaryInvariantT a (-c) (auxiliaryInvolution s)))
  rw [auxiliary_invariant_flow_involution_product]
  have hQ : auxiliaryQ a s = S := quinticAuxiliaryState_Q half η x y z t hhalf
  have hz : s.u - s.v = z := coordinateW_sub_coordinateV half x y z t hhalf
  rw [hQ, hz]
  have hU : coordinateU x' y' z t = coordinateU x y z t + η * scale * t ^ 3 * S := by
    unfold coordinateU x' y'
    ring
  have hP : coordinateP y' t = s.p - 2 * z * (c * S) := by
    change t * y' = coordinateP y t - 2 * z * (c * S)
    calc
      _ = t * y - scale * z * t ^ 2 * S := by dsimp only [y']; ring
      _ = _ := by
        change t * y - scale * z * t ^ 2 * S = t * y - 2 * z * (half * (scale * t ^ 2) * S)
        rw [show 2 * z * (half * (scale * t ^ 2) * S) = (2 * half) * (scale * z * t ^ 2 * S) by ring,
          hhalf, one_mul]
  have hV : coordinateV half x' y' z t = s.v + a * (c * S) := by
    change half * (coordinateU x' y' z t - z) =
      half * (coordinateU x y z t - z) + (η * t) * (half * (scale * t ^ 2) * S)
    rw [hU]
    ring
  have hW : coordinateW half x' y' z t = s.u + a * (c * S) := by
    change half * (coordinateU x' y' z t + z) =
      half * (coordinateU x y z t + z) + (η * t) * (half * (scale * t ^ 2) * S)
    rw [hU]
    ring
  unfold quinticAuxiliaryState
  rw [hP, hV, hW]

end DimensionFourDependence.Quintic
