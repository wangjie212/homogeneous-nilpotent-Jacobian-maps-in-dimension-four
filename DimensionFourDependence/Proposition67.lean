import DimensionFourDependence.QuinticGroupedTameWord
import DimensionFourDependence.QuinticInvolution
import DimensionFourDependence.QuinticInverseFlowLift
import DimensionFourDependence.QuadraticPencilShearTransport
import DimensionFourDependence.QuinticCommutatorAuxiliaryLift
import DimensionFourDependence.NormalizedQuinticShearCoordinates

/-! # Proposition 6.7 and the actual polynomial commutator (6.21) -/

namespace DimensionFourDependence.Quintic

open MvPolynomial

set_option maxHeartbeats 2100000

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

/-- The word is written in pullback order, so this is exactly the
point-map commutator G J G⁻¹ J in (6.21). -/
theorem normalized_quintic_shear_has_tame_commutator (η scale : K) :
    ∃ G : Aut₄, G ∈ Tame.subgroup K 4 ∧ G t = t ∧
      (b).map G.toRingHom = auxiliaryInvariantT (C η * t) (half * (C scale * t ^ 2)) b ∧
      Shear.automorphism4 (X 0 * X 1) (X 0 ^ 2 + C η * X 1 ^ 2) (C scale * X 0) =
        quinticInvolution * G⁻¹ * quinticInvolution * G := by
  obtain ⟨G, hG, hGt, hGb⟩ := quintic_invariant_T_is_tame η scale
  obtain ⟨N, _, hNt, hNb⟩ := quintic_invariant_T_is_tame η (-scale)
  have hN := quintic_sign_reversed_lift_is_inverse G N η scale hGt hNt hGb hNb
  let J : Aut₄ := quinticInvolution
  have hJt : J t = t := quinticInvolution_X 3
  have hJb : (b).map J.toRingHom = auxiliaryInvolution b := quinticInvolution_auxiliary_image
  let E := J * N * J * G
  obtain ⟨hEt, hEb⟩ := quintic_actual_word_auxiliary_image G N J η scale hGt hNt hJt hGb hNb hJb
  let F : Aut₄ := Shear.automorphism4 (X 0 * X 1) (X 0 ^ 2 + C η * X 1 ^ 2) (C scale * X 0)
  let S := quinticInvariant (C η) x y z t
  have hFx : F x = x + C scale * (z ^ 2 + C η * t ^ 2) * S := normalized_quintic_shear_X η scale 0
  have hFy : F y = y - C scale * (z * t) * S := normalized_quintic_shear_X η scale 1
  have hFz : F z = z := normalized_quintic_shear_X η scale 2
  have hFt : F t = t := normalized_quintic_shear_X η scale 3
  have hAuxF := quintic_auxiliary_state_after_substitution F _ _ _ hFx hFy hFz hFt
  have hAuxWord := quintic_shear_auxiliary_commutator half (C η) (C scale) x y z t
    original_quintic_half_identity
  have hAux : (b).map F.toRingHom = (b).map E.toRingHom :=
    hAuxF.trans (hAuxWord.trans hEb.symm)
  have hFE := quintic_automorphisms_eq_of_auxiliary_images F E hFt hEt hAux
  refine ⟨G, hG, hGt, hGb, ?_⟩
  change F = J * G⁻¹ * J * G
  exact hFE.trans (congrArg (fun A : Aut₄ => J * A * J * G) hN)

theorem proposition_6_7 : Shear.NormalizedQuadraticPencilShearsTame K := by
  intro η scale
  obtain ⟨G, hG, _, _, he⟩ := normalized_quintic_shear_has_tame_commutator η scale
  rw [he]
  let S := Tame.subgroup K 4
  have hJ : quinticInvolution (K := K) ∈ S := quinticInvolution_tame
  exact S.mul_mem (S.mul_mem (S.mul_mem hJ (S.inv_mem hG)) hJ) hG

end DimensionFourDependence.Quintic
