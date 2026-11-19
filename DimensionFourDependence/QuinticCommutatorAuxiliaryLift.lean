import DimensionFourDependence.QuinticAuxiliaryLiftFaithfulness

/-! # Substituting the actual commutator factors into the auxiliary state -/

namespace DimensionFourDependence.Quintic

open MvPolynomial

set_option maxHeartbeats 1200000

variable {K : Type*} [Field K] [CharZero K]
local notation "R₄" => MvPolynomial (Fin 4) K
local notation "Aut₄" => R₄ ≃ₐ[K] R₄
local notation "x" => (X 0 : R₄)
local notation "y" => (X 1 : R₄)
local notation "z" => (X 2 : R₄)
local notation "t" => (X 3 : R₄)
local notation "half" => (C (2 : K)⁻¹ : R₄)
local notation "b" => (quinticAuxiliaryState half x y z t)

theorem quintic_actual_word_auxiliary_image (G N J : Aut₄) (η scale : K)
    (hGt : G t = t) (hNt : N t = t) (hJt : J t = t)
    (hGb : (b).map G.toRingHom = auxiliaryInvariantT (C η * t) (half * (C scale * t ^ 2)) b)
    (hNb : (b).map N.toRingHom = auxiliaryInvariantT (C η * t) (half * (C (-scale) * t ^ 2)) b)
    (hJb : (b).map J.toRingHom = auxiliaryInvolution b) :
    let a := C η * t
    let c := half * (C scale * t ^ 2)
    let E := J * N * J * G
    E t = t ∧ (b).map E.toRingHom =
      auxiliaryInvariantT a c (auxiliaryInvolution (auxiliaryInvariantT a (-c) (auxiliaryInvolution b))) := by
  let E₁ := J * N
  let E₂ := E₁ * J
  let E₃ := E₂ * G
  have hE₁t : E₁ t = t := by change J (N t) = t; rw [hNt, hJt]
  have hE₂t : E₂ t = t := by change E₁ (J t) = t; rw [hJt, hE₁t]
  have hE₃t : E₃ t = t := by change E₂ (G t) = t; rw [hGt, hE₂t]
  let a := C η * t
  let c := half * (C scale * t ^ 2)
  have hneg : (half * (C (-scale) * t ^ 2) : R₄) = -c := by simp only [c, map_neg, neg_mul, mul_neg]
  have hE₁b : (b).map E₁.toRingHom = auxiliaryInvariantT a (-c) (auxiliaryInvolution b) := by
    change ((b).map N.toRingHom).map J.toRingHom = _
    rw [hNb, substitute_quintic_invariant_flow J hJt η (-scale), hJb, hneg]
  have hE₂b : (b).map E₂.toRingHom = auxiliaryInvolution (auxiliaryInvariantT a (-c) (auxiliaryInvolution b)) := by
    change ((b).map J.toRingHom).map E₁.toRingHom = _
    rw [hJb, map_auxiliaryInvolution, hE₁b]
  have hE₃b : (b).map E₃.toRingHom =
      auxiliaryInvariantT a c (auxiliaryInvolution (auxiliaryInvariantT a (-c) (auxiliaryInvolution b))) := by
    change ((b).map G.toRingHom).map E₂.toRingHom = _
    rw [hGb, substitute_quintic_invariant_flow E₂ hE₂t η scale, hE₂b]
  exact ⟨hE₃t, hE₃b⟩

end DimensionFourDependence.Quintic
