import DimensionFourDependence.QuinticSecondFlowTameWord
import DimensionFourDependence.QuinticSecondLiftAuxiliaryCoordinates
import DimensionFourDependence.QuinticGroupedAuxiliaryFactors

/-! # The actual tame lift of the second grouped conjugate, (6.41) -/

namespace DimensionFourDependence.Quintic

open MvPolynomial

set_option maxHeartbeats 1500000

variable {K : Type*} [Field K] [CharZero K]
local notation "R₂" => MvPolynomial (Fin 2) K
local notation "R₄" => MvPolynomial (Fin 4) K
local notation "Aut₄" => R₄ ≃ₐ[K] R₄
local notation "x" => (X 0 : R₄)
local notation "y" => (X 1 : R₄)
local notation "z" => (X 2 : R₄)
local notation "t" => (X 3 : R₄)
local notation "half" => (C (2 : K)⁻¹ : R₄)
local notation "s" => (ActiveState.mk x y z)
local notation "b" => (quinticAuxiliaryState half x y z t)

theorem quintic_grouped_second_is_tame (η scale : K) :
    ∃ E : Aut₄, E ∈ Tame.subgroup K 4 ∧ E t = t ∧
      (b).map E.toRingHom = groupedAuxiliarySecond (C η * t) half (C scale * t ^ 2) b := by
  let c : K := η * scale * (2 : K)⁻¹
  let g : R₂ := C c * X 1 ^ 2 + C (c * η) * X 1 ^ 4 * X 0
  let q := secondInvariant half t s
  let r := (b).u + half * auxiliaryq (C η * t) b
  let h := C η * C scale * t ^ 2 * r
  have hh : 2 * half = 1 := original_quintic_half_identity
  have hr : r = half * (q + 1 + C η * t ^ 2 * y) :=
    quintic_grouped_auxiliary_parameter half (C η) t s hh
  have hg : coefficientPlane g = C c * t ^ 2 + (C c * C η) * t ^ 4 * y := by
    have hC (d : K) : coefficientPlane (C d) = C d := coefficientPlane.commutes d
    have h₀ : coefficientPlane (X 0 : R₂) = y := aeval_X _ _
    have h₁ : coefficientPlane (X 1 : R₂) = t := aeval_X _ _
    simp only [g, map_add, map_mul, map_pow, hC, h₀, h₁]
  have hp : C c * t ^ 2 * q + coefficientPlane g = h := by
    rw [hg]
    change C c * t ^ 2 * q + (C c * t ^ 2 + (C c * C η) * t ^ 4 * y) =
      C η * C scale * t ^ 2 * r
    rw [hr]
    simp only [c, map_mul]
    ring
  obtain ⟨E, hE, hEt, hEs⟩ := quintic_shifted_second_flow_is_tame c g
  change (s).map E.toRingHom = secondLiftFlow half t (C c * t ^ 2 * q + coefficientPlane g) s at hEs
  rw [hp] at hEs
  refine ⟨E, hE, hEt, ?_⟩
  have hEhalf : E.toRingHom half = half := E.commutes _
  have hEt' : E.toRingHom t = t := hEt
  have haux := map_quinticAuxiliaryState E.toRingHom half t s
  rw [hEhalf, hEt'] at haux
  have ha := quintic_second_lift_auxiliary_coordinates half t h s hh
  dsimp only at ha
  calc
    (b).map E.toRingHom = ⟨(b).p, (b).v + t * h, (b).u + half * (2 * (b).v * (t * h) + (t * h) ^ 2)⟩ := by
      rw [haux]
      change quinticAuxiliaryState half ((s).map E.toRingHom).x ((s).map E.toRingHom).y
        ((s).map E.toRingHom).z t = _
      rw [hEs]
      exact ha
    _ = _ := by
      rw [groupedAuxiliarySecond_coordinates]
      have he : C η * t * (C scale * t ^ 2 * r) = t * h := by dsimp only [h]; ring
      change _ = AuxiliaryState.mk (b).p ((b).v + C η * t * (C scale * t ^ 2 * r))
        ((b).u + half * (2 * (b).v * (C η * t * (C scale * t ^ 2 * r)) +
          (C η * t * (C scale * t ^ 2 * r)) ^ 2))
      rw [he]

end DimensionFourDependence.Quintic
