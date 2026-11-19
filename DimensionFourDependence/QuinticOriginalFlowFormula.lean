import DimensionFourDependence.Proposition67
import DimensionFourDependence.QuinticPrintedFlowCoordinates

/-! # Agreement of the actual tame G with the printed formula (6.43) -/

namespace DimensionFourDependence.Quintic

open MvPolynomial

set_option maxHeartbeats 1300000

variable {K : Type*} [Field K] [CharZero K]
local notation "R₄" => MvPolynomial (Fin 4) K
local notation "Aut₄" => R₄ ≃ₐ[K] R₄
local notation "x" => (X 0 : R₄)
local notation "y" => (X 1 : R₄)
local notation "z" => (X 2 : R₄)
local notation "t" => (X 3 : R₄)
local notation "half" => (C (2 : K)⁻¹ : R₄)
local notation "s" => (ActiveState.mk x y z)
local notation "b" => (quinticAuxiliaryState half x y z t)

/-- The same invariant-flow lift used in the tame commutator has exactly
the coordinate polynomials printed in (6.43). -/
theorem quintic_invariant_T_original_coordinates (η scale : K) (G : Aut₄)
    (hGt : G t = t)
    (hGb : (b).map G.toRingHom = auxiliaryInvariantT (C η * t) (half * (C scale * t ^ 2)) b) :
    let c := C scale * quinticInvariant (C η) x y z t
    let w := invariantFlowCoordinates half (C η) c t s
    ∀ j, G (X j) = ![w.x, w.y, w.z, t] j := by
  let c := C scale * quinticInvariant (C η) x y z t
  let w := invariantFlowCoordinates half (C η) c t s
  have hh : 2 * half = 1 := original_quintic_half_identity
  have hq : auxiliaryQ (C η * t) b = quinticInvariant (C η) x y z t :=
    quinticAuxiliaryState_Q half (C η) x y z t hh
  have hp : t ^ 2 * (half * c) = (half * (C scale * t ^ 2)) * auxiliaryQ (C η * t) b := by
    rw [hq]
    dsimp only [c]
    ring
  have hw := invariantFlowCoordinates_auxiliary_image half (C η) c t s hh
  change quinticAuxiliaryState half w.x w.y w.z t =
    auxiliaryT (C η * t) (t ^ 2 * (half * c)) b at hw
  rw [hp] at hw
  have he : quinticAuxiliaryState half (G x) (G y) (G z) t =
      quinticAuxiliaryState half w.x w.y w.z t := by
    rw [← quintic_auxiliary_state_after_substitution G (G x) (G y) (G z) rfl rfl rfl hGt, hGb]
    exact hw.symm
  obtain ⟨hx, hy, hz⟩ := quintic_auxiliary_coordinates_injective half t (G x) (G y) (G z)
    w.x w.y w.z hh (X_ne_zero 3) (congrArg AuxiliaryState.p he)
    (congrArg AuxiliaryState.v he) (congrArg AuxiliaryState.u he)
  change ∀ j : Fin 4, G (X j) = ![w.x, w.y, w.z, t] j
  intro j
  fin_cases j
  · exact hx
  · exact hy
  · exact hz
  · exact hGt

end DimensionFourDependence.Quintic
