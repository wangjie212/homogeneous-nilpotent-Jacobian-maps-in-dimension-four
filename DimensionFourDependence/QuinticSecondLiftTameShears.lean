import DimensionFourDependence.QuinticPlaneShears
import DimensionFourDependence.QuinticParameterShifting
import DimensionFourDependence.QuinticCoefficientPlaneTranslations

/-! # The actual determinant shears in the second grouped factor -/

namespace DimensionFourDependence.Quintic

open MvPolynomial

set_option maxHeartbeats 1100000

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

theorem original_quintic_half_identity : 2 * half = (1 : R₄) := by
  rw [← map_ofNat (C : K →+* R₄) 2, ← map_mul, mul_inv_cancel₀ two_ne_zero, map_one]

/-- Equation (6.37), including a scalar on its invariant parameter. -/
theorem quintic_parameter_shift_is_tame (c : K) :
    ∃ P : Aut₄, P ∈ Tame.subgroup K 4 ∧
      let q := C c * secondInvariant half t s
      ∀ j, P (X j) = ![x - z * q, y + t * q, z, t] j := by
  let f : R₃ := C c * (2 * X 2 - (C (2 : K)⁻¹ * (X 0 - X 2) - 1) ^ 2)
  let U := coordinateU x y z t
  let E : R₃ →ₐ[K] R₄ := aeval ![U, t, z]
  have hE : E f = C c * secondInvariant half t s := by
    have hC (d : K) : E (C d) = C d := E.commutes d
    have h₀ : E (X 0) = U := aeval_X _ _
    have h₂ : E (X 2) = z := aeval_X _ _
    simp only [f, map_mul, map_sub, map_pow, map_ofNat, map_one, hC, h₀, h₂]
    change C c * (2 * z - (half * (t * x + z * y - z) - 1) ^ 2) =
      C c * (2 * z - (half * (t * x + (y - 1) * z) - 1) ^ 2)
    rw [show t * x + z * y - z = t * x + (y - 1) * z by ring]
  obtain ⟨P, hP, h⟩ := tame_xy_invariant_shear f
  change ∀ j : Fin 4, P (X j) = ![x - z * E f, y + t * E f, z, t] j at h
  rw [hE] at h
  exact ⟨P, hP, h⟩

/-- The middle factor of (6.36), given an arbitrary polynomial h(y,t). -/
theorem quintic_second_lift_middle_factor (h : R₂) :
    ∃ M : Aut₄, M ∈ Tame.subgroup K 4 ∧
      ∀ j, M (X j) = ![x + (1 - y) * coefficientPlane h * omega half t s, y,
        z + t * coefficientPlane h * omega half t s, t] j := by
  let β := y + C (-1 : K)
  let Δ := t * x + β * z
  let E : R₃ →ₐ[K] R₄ := aeval ![Δ, t, β]
  let U : R₂ →ₐ[K] R₃ := aeval ![X 2 + 1, X 1]
  let f : R₃ := -(U h * (C (2 : K)⁻¹ * X 0 - 1))
  have eβ : β = y - 1 := by simp [β, sub_eq_add_neg]
  have eU : E.comp U = coefficientPlane := by
    apply MvPolynomial.algHom_ext
    intro i
    simp only [AlgHom.comp_apply, U, aeval_X, coefficientPlane]
    fin_cases i
    · change E (X 2 + 1) = y
      rw [map_add, map_one, show E (X 2) = β from aeval_X _ _, eβ, sub_add_cancel]
    · exact aeval_X _ _
  have eh : E (U h) = coefficientPlane h := AlgHom.congr_fun eU h
  have ef : E f = -(coefficientPlane h * omega half t s) := by
    have eΔ : E (X 0) = Δ := aeval_X _ _
    have eC : E (C (2 : K)⁻¹) = half := E.commutes _
    simp only [f, map_neg, map_mul, map_sub, map_one, eh, eC, eΔ, Δ, eβ, omega]
  obtain ⟨M, hM, hX⟩ := tame_xz_invariant_shear (-1 : K) f
  change ∀ j : Fin 4, M (X j) = ![x + β * E f, y, z - t * E f, t] j at hX
  rw [ef, eβ] at hX
  refine ⟨M, hM, ?_⟩
  intro j
  have hj := hX j
  fin_cases j
  · change M x = x + (1 - y) * coefficientPlane h * omega half t s
    calc
      _ = x + (y - 1) * -(coefficientPlane h * omega half t s) := hj
      _ = _ := by ring
  · exact hj
  · change M z = z + t * coefficientPlane h * omega half t s
    calc
      _ = z - t * -(coefficientPlane h * omega half t s) := hj
      _ = _ := by ring
  · exact hj

end DimensionFourDependence.Quintic
