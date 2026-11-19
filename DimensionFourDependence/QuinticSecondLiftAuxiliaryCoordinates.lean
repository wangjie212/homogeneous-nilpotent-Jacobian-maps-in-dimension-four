import DimensionFourDependence.QuinticStateSubstitution

/-! # The polynomial coordinates of the second grouped lift, (6.32)–(6.35) -/

namespace DimensionFourDependence.Quintic

variable {R : Type*} [CommRing R]

theorem quintic_auxiliary_v_eq_omega_add_one (half t : R) (s : ActiveState R) :
    (quinticAuxiliaryState half s.x s.y s.z t).v = omega half t s + 1 := by
  unfold quinticAuxiliaryState coordinateV coordinateU omega
  ring

theorem quintic_auxiliary_u_eq_v_add_z (half t : R) (s : ActiveState R) (hh : 2 * half = 1) :
    let b := quinticAuxiliaryState half s.x s.y s.z t
    b.u = b.v + s.z := by
  let b := quinticAuxiliaryState half s.x s.y s.z t
  have h : b.u - b.v = s.z := coordinateW_sub_coordinateV _ _ _ _ _ hh
  exact sub_eq_iff_eq_add.mp h |>.trans (add_comm _ _)

theorem quintic_grouped_auxiliary_parameter (half η t : R) (s : ActiveState R) (hh : 2 * half = 1) :
    let b := quinticAuxiliaryState half s.x s.y s.z t
    b.u + half * auxiliaryq (η * t) b =
      half * (secondInvariant half t s + 1 + η * t ^ 2 * s.y) := by
  let b := quinticAuxiliaryState half s.x s.y s.z t
  change b.u + half * auxiliaryq (η * t) b = _
  have hV : b.v = omega half t s + 1 := quintic_auxiliary_v_eq_omega_add_one half t s
  have hU : b.u = b.v + s.z := quintic_auxiliary_u_eq_v_add_z half t s hh
  have hp : b.p = t * s.y := rfl
  rw [hU, auxiliaryq, hV, hp, secondInvariant]
  linear_combination -(omega half t s + 1 + s.z) * hh

theorem quintic_second_lift_auxiliary_coordinates (half t h : R) (s : ActiveState R)
    (hh : 2 * half = 1) :
    let b := quinticAuxiliaryState half s.x s.y s.z t
    let w := secondLiftFlow half t h s
    let c := t * h
    quinticAuxiliaryState half w.x w.y w.z t =
      ⟨b.p, b.v + c, b.u + half * (2 * b.v * c + c ^ 2)⟩ := by
  let b := quinticAuxiliaryState half s.x s.y s.z t
  let w := secondLiftFlow half t h s
  let b' := quinticAuxiliaryState half w.x w.y w.z t
  let c := t * h
  have hp : b'.p = b.p := rfl
  have hv : b'.v = b.v + c := by
    have h₁ : b'.v = omega half t w + 1 := quintic_auxiliary_v_eq_omega_add_one half t w
    have h₂ : b.v = omega half t s + 1 := quintic_auxiliary_v_eq_omega_add_one half t s
    have h₃ : omega half t w = omega half t s + c := secondLiftFlow_omega half t h s hh
    rw [h₁, h₂, h₃]
    ring
  have hu : b'.u = b.u + half * (2 * b.v * c + c ^ 2) := by
    have h₁ : b'.u = b'.v + w.z := quintic_auxiliary_u_eq_v_add_z half t w hh
    have h₂ : b.u = b.v + s.z := quintic_auxiliary_u_eq_v_add_z half t s hh
    have h₃ : b.v = omega half t s + 1 := quintic_auxiliary_v_eq_omega_add_one half t s
    have hz : w.z = s.z + t * omega half t s * h + t ^ 2 * half * h ^ 2 := rfl
    rw [h₁, hv, h₂, h₃, hz]
    dsimp only [c]
    linear_combination -((omega half t s + 1) * t * h) * hh
  change b' = ⟨b.p, b.v + c, b.u + half * (2 * b.v * c + c ^ 2)⟩
  rw [← hp, ← hv, ← hu]

end DimensionFourDependence.Quintic
