import DimensionFourDependence.QuinticPlaneShears
import DimensionFourDependence.QuinticCoefficientPlaneTranslations
import DimensionFourDependence.QuinticFirstLiftAuxiliaryCoordinates

/-! # The actual triangular frame and the tame shear in that frame -/

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

/-- The three transformed coordinates in (6.30) come from products
of elementary translations with coefficients in y,t. -/
theorem quintic_first_lift_frame_is_tame (η : K) :
    ∃ A : Aut₄, A ∈ Tame.subgroup K 4 ∧
      let w := firstLiftFrame half (C η) t s
      ∀ i, A (X i) = ![w.x, w.y, w.z, t] i := by
  let p : R₂ := -(C η * X 1 * C (2 : K)⁻¹ * (X 0 ^ 2 - X 0))
  let q : R₂ := C η * X 1 ^ 2 * C (2 : K)⁻¹ * X 0
  obtain ⟨A, hA, h⟩ := coefficientPlane_double_translation p q
  refine ⟨A, hA, ?_⟩
  let w := firstLiftFrame half (C η) t s
  change ∀ i : Fin 4, A (X i) = ![w.x, w.y, w.z, t] i
  have hC (c : K) : coefficientPlane (C c) = C c := coefficientPlane.commutes _
  have h₀ : coefficientPlane (X 0 : R₂) = y := aeval_X _ _
  have h₁ : coefficientPlane (X 1 : R₂) = t := aeval_X _ _
  intro i
  fin_cases i
  · change A x = x - C η * t * half * (y ^ 2 - y)
    have hx : A x = x + coefficientPlane p := h 0
    simpa only [p, map_neg, map_mul, map_add, map_sub, map_pow, hC, h₀, h₁, sub_eq_add_neg] using hx
  · exact h 1
  · change A z = z + C η * t ^ 2 * half * y
    have hz : A z = z + coefficientPlane q := h 2
    simpa only [q, map_mul, map_pow, hC, h₀, h₁] using hz
  · exact h 3

/-- Conjugate the original xy shear by an actual tame frame, with
the polynomial parameter transported along the whole substitution. -/
theorem tame_xy_invariant_shear_in_frame (A : Aut₄) (hA : A ∈ Tame.subgroup K 4) (f : R₃) :
    ∃ E : Aut₄, E ∈ Tame.subgroup K 4 ∧
      let u := coordinateU (A x) (A y) (A z) (A t)
      let k := aeval ![u, A t, A z] f
      E (A x) = A x - A z * k ∧ E (A y) = A y + A t * k ∧
        E (A z) = A z ∧ E (A t) = A t := by
  obtain ⟨F, hF, hX⟩ := tame_xy_invariant_shear f
  let E := A * F * A⁻¹
  let d := coordinateU x y z t
  let k₀ := aeval ![d, t, z] f
  let d' := coordinateU (A x) (A y) (A z) (A t)
  let k := aeval ![d', A t, A z] f
  have he (j : Fin 4) : E (A (X j)) = A (F (X j)) := by simp [E, AlgEquiv.mul_apply]
  have hd : A d = d' := by simp only [d, d', coordinateU, map_add, map_mul]
  have hv : (fun j : Fin 3 => A.toAlgHom (![d, t, z] j)) = ![d', A t, A z] := by
    funext j
    fin_cases j
    · exact hd
    · rfl
    · rfl
  have hk : A k₀ = k := by
    change A.toAlgHom (aeval ![d, t, z] f) = _
    rw [Tame.algHom_aeval, hv]
  refine ⟨E, (Tame.subgroup K 4).mul_mem ((Tame.subgroup K 4).mul_mem hA hF)
    ((Tame.subgroup K 4).inv_mem hA), ?_⟩
  change E (A x) = A x - A z * k ∧ E (A y) = A y + A t * k ∧ E (A z) = A z ∧ E (A t) = A t
  have hx : F x = x - z * k₀ := hX 0
  have hy : F y = y + t * k₀ := hX 1
  have hz : F z = z := hX 2
  have ht : F t = t := hX 3
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [he, hx, map_sub, map_mul, hk]
  · rw [he, hy, map_add, map_mul, hk]
  · rw [he, hz]
  · rw [he, ht]

end DimensionFourDependence.Quintic
