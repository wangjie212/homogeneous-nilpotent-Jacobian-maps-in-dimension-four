import DimensionFourDependence.QuinticSecondLiftTameShears

/-! # The tame polynomial realization of V_h, equation (6.36) -/

namespace DimensionFourDependence.Quintic

open MvPolynomial

set_option maxHeartbeats 1200000

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

/-- For every polynomial in y,t, the displayed flow is a product of
two elementary translations and a determinant shear, all over K. -/
theorem quintic_second_flow_is_tame (h : R₂) :
    ∃ V : Aut₄, V ∈ Tame.subgroup K 4 ∧
      let w := secondLiftFlow half t (coefficientPlane h) s
      ∀ j, V (X j) = ![w.x, w.y, w.z, t] j := by
  let u := coefficientPlane h
  let d : R₂ := (1 - X 0) * X 1 * C (2 : K)⁻¹ * h ^ 2
  let e : R₂ := X 1 ^ 2 * C (2 : K)⁻¹ * h ^ 2
  obtain ⟨ρ, hρtame, hρ⟩ := coefficientPlane_double_translation d e
  obtain ⟨σ, hσtame, hσ⟩ := quintic_second_lift_middle_factor h
  obtain ⟨τ, hτtame, hτ⟩ := coefficientPlane_double_translation (2 * h) 0
  have hβ (c : K) : coefficientPlane (C c) = C c := coefficientPlane.commutes c
  have h₀ : coefficientPlane (X 0 : R₂) = y := aeval_X _ _
  have h₁ : coefficientPlane (X 1 : R₂) = t := aeval_X _ _
  have hρx : ρ x = x + (1 - y) * t * half * u ^ 2 := by
    change ρ x = x + (1 - y) * t * half * u ^ 2
    have he : ρ x = x + coefficientPlane d := hρ 0
    simpa only [d, map_mul, map_sub, map_pow, hβ, h₀, h₁, map_one, u] using he
  have hρy : ρ y = y := hρ 1
  have hρz : ρ z = z + t ^ 2 * half * u ^ 2 := by
    have he : ρ z = z + coefficientPlane e := hρ 2
    simpa only [e, map_mul, map_pow, hβ, h₁, u] using he
  have hρt : ρ t = t := hρ 3
  have hρu : ρ u = u := coefficientPlane_fixed ρ hρy hρt h
  have hρhalf : ρ half = half := ρ.commutes _
  let ω := omega half t s
  have hρomega : ρ ω = ω := by
    change ρ (half * (t * x + (y - 1) * z) - 1) = half * (t * x + (y - 1) * z) - 1
    simp only [map_sub, map_add, map_mul, map_one, hρhalf, hρt, hρx, hρy, hρz]
    ring
  have hσx : σ x = x + (1 - y) * u * ω := hσ 0
  have hσy : σ y = y := hσ 1
  have hσz : σ z = z + t * u * ω := hσ 2
  have hσt : σ t = t := hσ 3
  have hσu : σ u = u := coefficientPlane_fixed σ hσy hσt h
  have hτx : τ x = x + 2 * u := by
    have he : τ x = x + coefficientPlane (2 * h) := hτ 0
    simpa only [map_mul, map_ofNat, u] using he
  have hτy : τ y = y := hτ 1
  have hτz : τ z = z := by
    have he : τ z = z + coefficientPlane 0 := hτ 2
    simpa only [map_zero, add_zero] using he
  have hτt : τ t = t := hτ 3
  let V := ρ * σ * τ
  let w := secondLiftFlow half t u s
  refine ⟨V, (Tame.subgroup K 4).mul_mem
    ((Tame.subgroup K 4).mul_mem hρtame hσtame) hτtame, ?_⟩
  change ∀ j : Fin 4, V (X j) = ![w.x, w.y, w.z, t] j
  intro j
  fin_cases j
  · change ρ (σ (τ x)) = x + u * (2 + (1 - y) * ω) + (1 - y) * t * half * u ^ 2
    simp only [hτx, map_add, map_mul, map_ofNat, hσx, hσu, hρx, map_sub, map_one,
      hρy, hρu, hρomega]
    ring
  · change ρ (σ (τ y)) = y
    rw [hτy, hσy, hρy]
  · change ρ (σ (τ z)) = z + t * ω * u + t ^ 2 * half * u ^ 2
    simp only [hτz, hσz, map_add, map_mul, hρz, hρt, hρu, hρomega]
    ring
  · change ρ (σ (τ t)) = t
    rw [hτt, hσt, hρt]

end DimensionFourDependence.Quintic
