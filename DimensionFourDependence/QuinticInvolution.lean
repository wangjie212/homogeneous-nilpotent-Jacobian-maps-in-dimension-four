import DimensionFourDependence.QuinticAuxiliaryLiftFaithfulness

/-! # The actual affine involution used in the quintic commutator -/

namespace DimensionFourDependence.Quintic

open MvPolynomial

variable {K : Type*} [Field K]
local notation "R₄" => MvPolynomial (Fin 4) K
local notation "Aut₄" => R₄ ≃ₐ[K] R₄
local notation "x" => (X 0 : R₄)
local notation "y" => (X 1 : R₄)
local notation "z" => (X 2 : R₄)
local notation "t" => (X 3 : R₄)
local notation "half" => (C (2 : K)⁻¹ : R₄)
local notation "b" => (quinticAuxiliaryState half x y z t)

noncomputable def quinticInvolution : Aut₄ :=
  AlgEquiv.ofAlgHom (aeval (![x, -y, -z, t] : Fin 4 → R₄))
    (aeval (![x, -y, -z, t] : Fin 4 → R₄))
    (by apply MvPolynomial.algHom_ext; intro i; fin_cases i <;> simp)
    (by apply MvPolynomial.algHom_ext; intro i; fin_cases i <;> simp)

theorem quinticInvolution_X (j : Fin 4) :
    quinticInvolution (X j : R₄) = ![x, -y, -z, t] j :=
  aeval_X _ _

theorem quinticInvolution_tame : quinticInvolution (K := K) ∈ Tame.subgroup K 4 := by
  apply Subgroup.subset_closure
  left
  intro j
  rw [quinticInvolution_X]
  fin_cases j <;> simp

theorem quinticInvolution_auxiliary_image [CharZero K] :
    (b).map (quinticInvolution (K := K)).toRingHom = auxiliaryInvolution b := by
  rw [quintic_auxiliary_state_after_substitution quinticInvolution x (-y) (-z)
    (quinticInvolution_X 0) (quinticInvolution_X 1) (quinticInvolution_X 2) (quinticInvolution_X 3)]
  exact quinticAuxiliaryState_involution half x y z t

end DimensionFourDependence.Quintic
