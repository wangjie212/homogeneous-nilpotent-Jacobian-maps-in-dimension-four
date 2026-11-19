import DimensionFourDependence.QuinticAuxiliaryLiftFaithfulness

/-! # The sign-reversed invariant flow gives the actual inverse lift -/

namespace DimensionFourDependence.Quintic

open MvPolynomial

set_option maxHeartbeats 1200000

variable {R : Type*} [CommRing R]

theorem auxiliaryInvariantT_comp_inverse (a c : R) (s : AuxiliaryState R) :
    auxiliaryInvariantT a c (auxiliaryInvariantT a (-c) s) = s := by
  unfold auxiliaryInvariantT
  rw [auxiliaryT_preserves_Q, auxiliaryT_comp_parameter_add, neg_mul, add_neg_cancel]
  cases s
  simp [auxiliaryT]

variable {K : Type*} [Field K] [CharZero K]
local notation "R₄" => MvPolynomial (Fin 4) K
local notation "Aut₄" => R₄ ≃ₐ[K] R₄
local notation "x" => (X 0 : R₄)
local notation "y" => (X 1 : R₄)
local notation "z" => (X 2 : R₄)
local notation "t" => (X 3 : R₄)
local notation "half" => (C (2 : K)⁻¹ : R₄)
local notation "b" => (quinticAuxiliaryState half x y z t)

theorem quintic_sign_reversed_lift_is_inverse (G N : Aut₄) (η scale : K)
    (hGt : G t = t) (hNt : N t = t)
    (hG : (b).map G.toRingHom = auxiliaryInvariantT (C η * t) (half * (C scale * t ^ 2)) b)
    (hN : (b).map N.toRingHom = auxiliaryInvariantT (C η * t) (half * (C (-scale) * t ^ 2)) b) :
    N = G⁻¹ := by
  have hTG : (N * G) t = t := by
    change N (G t) = t
    rw [hGt, hNt]
  have hb : (b).map (N * G).toRingHom = b := by
    change ((b).map G.toRingHom).map N.toRingHom = _
    rw [hG, substitute_quintic_invariant_flow N hNt, hN]
    rw [show (half * (C (-scale) * t ^ 2) : R₄) = -(half * (C scale * t ^ 2)) by
      simp only [map_neg, neg_mul, mul_neg]]
    exact auxiliaryInvariantT_comp_inverse _ _ _
  have h : N * G = 1 :=
    quintic_automorphisms_eq_of_auxiliary_images (N * G) 1 hTG rfl hb
  calc
    N = N * G * G⁻¹ := by rw [mul_assoc, mul_inv_cancel, mul_one]
    _ = G⁻¹ := by rw [h, one_mul]

end DimensionFourDependence.Quintic
