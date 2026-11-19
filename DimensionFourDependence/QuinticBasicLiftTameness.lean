import DimensionFourDependence.QuinticBasicLiftCoordinates
import DimensionFourDependence.QuinticSecondLiftTameShears

/-! # Tame polynomial lifts of the two elementary auxiliary shifts -/

namespace DimensionFourDependence.Quintic

open MvPolynomial

set_option maxHeartbeats 1400000

variable {K : Type*} [Field K] [CharZero K]
local notation "R₂" => MvPolynomial (Fin 2) K
local notation "R₃" => MvPolynomial (Fin 3) K
local notation "R₄" => MvPolynomial (Fin 4) K
local notation "Aut₄" => R₄ ≃ₐ[K] R₄
local notation "x" => (X 0 : R₄)
local notation "y" => (X 1 : R₄)
local notation "z" => (X 2 : R₄)
local notation "t" => (X 3 : R₄)
local notation "half" => (C (2 : K)⁻¹ : R₄)
local notation "s" => (ActiveState.mk x y z)
local notation "b" => (quinticAuxiliaryState half x y z t)

theorem quintic_auxiliary_state_after_substitution (E : Aut₄) (hx hy hz : R₄)
    (h₀ : E x = hx) (h₁ : E y = hy) (h₂ : E z = hz) (ht : E t = t) :
    (b).map E.toRingHom = quinticAuxiliaryState half hx hy hz t := by
  have he := map_quinticAuxiliaryState E.toRingHom half t s
  change (b).map E.toRingHom = quinticAuxiliaryState (E half) (E x) (E y) (E z) (E t) at he
  have hhalf : E half = half := E.commutes _
  rw [hhalf, h₀, h₁, h₂, ht] at he
  exact he

theorem quintic_auxiliary_p_shift_is_tame (f : R₃) :
    ∃ E : Aut₄, E ∈ Tame.subgroup K 4 ∧ E t = t ∧
      let κ := aeval ![coordinateU x y z t, t, z] f
      (b).map E.toRingHom = auxiliaryPShift (t ^ 2 * κ) b := by
  let κ := aeval ![coordinateU x y z t, t, z] f
  obtain ⟨E, hE, hX⟩ := tame_xy_invariant_shear f
  have hx : E x = x - z * κ := hX 0
  have hy : E y = y + t * κ := hX 1
  have hz : E z = z := hX 2
  have ht : E t = t := hX 3
  refine ⟨E, hE, ht, ?_⟩
  rw [quintic_auxiliary_state_after_substitution E _ _ _ hx hy hz ht]
  exact quintic_basic_p_lift_coordinates half t κ s

theorem quintic_auxiliary_v_shift_is_tame (η : K) (g : R₂) :
    ∃ E : Aut₄, E ∈ Tame.subgroup K 4 ∧ E t = t ∧
      let h := t ^ 2 * aeval ![(b).u, t] g
      (b).map E.toRingHom = auxiliaryVShift (C η * t * h) b := by
  let β : R₄ := y + 1
  let Δ : R₄ := t * x + β * z
  let E₃ : R₃ →ₐ[K] R₄ := aeval ![Δ, t, β]
  let U : R₂ →ₐ[K] R₃ := aeval ![C (2 : K)⁻¹ * X 0, X 1]
  let G := aeval (![(b).u, t] : Fin 2 → R₄) g
  let h := t ^ 2 * G
  let f : R₃ := C η * X 1 ^ 2 * U g
  have hU : half * Δ = (b).u := by
    change half * (t * x + (y + 1) * z) = half * (t * x + z * y + z)
    ring
  have hcomp : E₃.comp U = aeval ![(b).u, t] := by
    apply MvPolynomial.algHom_ext
    intro j
    simp only [U, AlgHom.comp_apply, aeval_X]
    fin_cases j
    · change E₃ (C (2 : K)⁻¹ * X 0) = (b).u
      rw [map_mul, show E₃ (C (2 : K)⁻¹) = half from E₃.commutes _,
        show E₃ (X 0) = Δ from aeval_X _ _, hU]
    · exact aeval_X _ _
  have hG : E₃ (U g) = G := AlgHom.congr_fun hcomp g
  have hf : E₃ f = C η * h := by
    have hC : E₃ (C η) = C η := E₃.commutes _
    have ht : E₃ (X 1) = t := aeval_X _ _
    simp only [f, map_mul, map_pow, hC, ht, hG, h, mul_assoc]
  obtain ⟨E, hE, hX⟩ := tame_xz_invariant_shear (1 : K) f
  have hβ : y + C (1 : K) = β := by simp [β]
  have hX' : ∀ j : Fin 4, E (X j) = ![x + β * E₃ f, y, z - t * E₃ f, t] j := by
    simpa only [hβ, E₃, Δ] using hX
  have hx : E x = x + C η * (1 + y) * h := by
    have he : E x = x + β * E₃ f := hX' 0
    rw [he, hf]
    dsimp only [β]
    ring
  have hy : E y = y := hX' 1
  have hz : E z = z - C η * t * h := by
    have he : E z = z - t * E₃ f := hX' 2
    rw [he, hf]
    ring
  have ht : E t = t := hX' 3
  refine ⟨E, hE, ht, ?_⟩
  rw [quintic_auxiliary_state_after_substitution E _ _ _ hx hy hz ht]
  exact quintic_basic_v_lift_coordinates half (C η) t h s original_quintic_half_identity

end DimensionFourDependence.Quintic
