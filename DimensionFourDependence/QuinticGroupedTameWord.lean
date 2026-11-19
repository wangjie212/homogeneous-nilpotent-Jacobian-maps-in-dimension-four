import DimensionFourDependence.QuinticGroupedFirstTameness
import DimensionFourDependence.QuinticGroupedSecondTameness
import DimensionFourDependence.QuinticAuxiliaryOnlyFlowTameness

/-! # The actual tame word for G in equation (6.42) -/

namespace DimensionFourDependence.Quintic

open MvPolynomial

set_option maxHeartbeats 1800000

variable {K : Type*} [Field K] [CharZero K]
local notation "R₂" => MvPolynomial (Fin 2) K
local notation "R₄" => MvPolynomial (Fin 4) K
local notation "Aut₄" => R₄ ≃ₐ[K] R₄
local notation "x" => (X 0 : R₄)
local notation "y" => (X 1 : R₄)
local notation "z" => (X 2 : R₄)
local notation "t" => (X 3 : R₄)
local notation "half" => (C (2 : K)⁻¹ : R₄)
local notation "b" => (quinticAuxiliaryState half x y z t)

/-- The auxiliary invariant flow is realized by the actual four
polynomial tame factors in (6.42), all of which fix t. -/
theorem quintic_invariant_T_is_tame (η scale : K) :
    ∃ G : Aut₄, G ∈ Tame.subgroup K 4 ∧ G t = t ∧
      (b).map G.toRingHom = auxiliaryInvariantT (C η * t) (half * (C scale * t ^ 2)) b := by
  let a : R₄ := C η * t
  let k : R₄ := C scale * t ^ 2
  let g₁ : R₂ := C (scale * (2 : K)⁻¹) * X 0 ^ 2
  let g₂ : R₂ := -(C scale * X 0)
  let w₁ := auxiliaryT a (half * k * (b).u ^ 2) b
  let w₂ := auxiliaryT a (-k * w₁.u) w₁
  let w₃ := groupedAuxiliarySecond a half k w₂
  let w₄ := groupedAuxiliaryFirst a half k w₃
  let D : R₂ →ₐ[K] R₄ := aeval ![(b).u, t]
  have hD (c : K) : D (C c) = C c := D.commutes _
  have hD₀ : D (X 0) = (b).u := aeval_X _ _
  have h₁ : t ^ 2 * D g₁ = half * k * (b).u ^ 2 := by
    simp only [g₁, k, map_mul, map_pow, hD, hD₀]
    ring
  have h₂ : t ^ 2 * D g₂ = -k * (b).u := by
    simp only [g₂, k, map_neg, map_mul, hD, hD₀]
    ring
  obtain ⟨C₀, hC₀, hC₀t, hC₀b⟩ := quintic_auxiliary_only_flow_is_tame η g₁
  obtain ⟨B, hB, hBt, hBb⟩ := quintic_auxiliary_only_flow_is_tame η g₂
  obtain ⟨E₂, hE₂, hE₂t, hE₂b⟩ := quintic_grouped_second_is_tame η scale
  obtain ⟨E₁, hE₁, hE₁t, hE₁b⟩ := quintic_grouped_first_is_tame η scale
  change (b).map C₀.toRingHom = auxiliaryT a (t ^ 2 * D g₁) b at hC₀b
  change (b).map B.toRingHom = auxiliaryT a (t ^ 2 * D g₂) b at hBb
  rw [h₁] at hC₀b
  rw [h₂] at hBb
  have hconstant (F : Aut₄) (hFt : F t = t) :
      F.toRingHom a = a ∧ F.toRingHom k = k ∧ F.toRingHom half = half := by
    have ht : F.toRingHom t = t := hFt
    have hC (c : K) : F.toRingHom (C c : R₄) = C c := F.commutes _
    simp only [a, k, map_mul, map_pow, ht, hC, and_self]
  let G₂ := C₀ * B
  let G₃ := G₂ * E₂
  let G₄ := G₃ * E₁
  have hG₂t : G₂ t = t := by change C₀ (B t) = t; rw [hBt, hC₀t]
  have hG₃t : G₃ t = t := by change G₂ (E₂ t) = t; rw [hE₂t, hG₂t]
  have hG₄t : G₄ t = t := by change G₃ (E₁ t) = t; rw [hE₁t, hG₃t]
  have hG₂b : (b).map G₂.toRingHom = w₂ := by
    change ((b).map B.toRingHom).map C₀.toRingHom = _
    have hu : C₀.toRingHom (b).u = w₁.u := congrArg AuxiliaryState.u hC₀b
    obtain ⟨ha, hk, _⟩ := hconstant C₀ hC₀t
    have hparam : C₀.toRingHom (-k * (b).u) = -k * w₁.u := by
      simp only [map_mul, map_neg, hk, hu]
    rw [hBb, map_auxiliaryT, ha, hparam, hC₀b]
  have hG₃b : (b).map G₃.toRingHom = w₃ := by
    change ((b).map E₂.toRingHom).map G₂.toRingHom = _
    change (b).map E₂.toRingHom = groupedAuxiliarySecond a half k b at hE₂b
    obtain ⟨ha, hk, hh⟩ := hconstant G₂ hG₂t
    rw [hE₂b, map_groupedAuxiliarySecond, ha, hk, hh, hG₂b]
  have hG₄b : (b).map G₄.toRingHom = w₄ := by
    change ((b).map E₁.toRingHom).map G₃.toRingHom = _
    change (b).map E₁.toRingHom = groupedAuxiliaryFirst a half k b at hE₁b
    obtain ⟨ha, hk, hh⟩ := hconstant G₃ hG₃t
    rw [hE₁b, map_groupedAuxiliaryFirst, ha, hk, hh, hG₃b]
  have hG : G₄ ∈ Tame.subgroup K 4 := (Tame.subgroup K 4).mul_mem
    ((Tame.subgroup K 4).mul_mem ((Tame.subgroup K 4).mul_mem hC₀ hB) hE₂) hE₁
  refine ⟨G₄, hG, hG₄t, ?_⟩
  rw [hG₄b]
  change groupedAuxiliaryFirst a half k (groupedAuxiliarySecond a half k w₂) =
    auxiliaryInvariantT a (half * k) b
  rw [groupedAuxiliaryFirst_comp_second]
  exact auxiliary_invariant_T_grouping a half k b

end DimensionFourDependence.Quintic
