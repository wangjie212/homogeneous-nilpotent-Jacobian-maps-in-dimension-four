import DimensionFourDependence.SplitDeterminantShearFactorization

/-! # The alpha-only parameter case of Lemma 6.2 -/

namespace DimensionFourDependence.DeterminantShear

open Matrix MvPolynomial

set_option maxHeartbeats 3000000

variable {K : Type*} [Field K] [CharZero K]

theorem alpha_only_parameter4 (f : MvPolynomial (Fin 2) K) :
    parameter4 (aeval ![X 0, X 1] f) = (aeval ![invariant4, X 2] f : MvPolynomial (Fin 4) K) := by
  unfold parameter4
  rw [comp_aeval_apply]
  have hg : (fun i : Fin 2 =>
      (aeval (![invariant4, X 2, X 3] : Fin 3 → MvPolynomial (Fin 4) K))
        ((![X 0, X 1] : Fin 2 → MvPolynomial (Fin 3) K) i)) = ![invariant4, X 2] := by
    funext i
    fin_cases i <;> simp
  exact congrArg (fun g : Fin 2 → MvPolynomial (Fin 4) K => aeval g f) hg

theorem splitInverseEquiv4_half_value (f : MvPolynomial (Fin 2) K) :
    splitInverseEquiv4 (splitHalfValue4 f) =
      C (2 : K)⁻¹ * (aeval ![invariant4, X 2] f : MvPolynomial (Fin 4) K) := by
  have hC (c : K) : splitInverseEquiv4 (C c) = (C c : MvPolynomial (Fin 4) K) :=
    splitInverseEquiv4.commutes c
  rw [splitHalfValue4, map_mul, hC]
  change C (2 : K)⁻¹ * splitInverseEquiv4.toAlgHom (aeval ![splitInvariant4, X 3] f) = _
  rw [Tame.algHom_aeval]
  have hg : (fun i : Fin 2 => splitInverseEquiv4 (![splitInvariant4, X 3] i)) =
      (![invariant4, X 2] : Fin 2 → MvPolynomial (Fin 4) K) := by
    funext i
    fin_cases i <;> simp [splitInverseEquiv4_invariant, splitInverseEquiv4_X]
  simpa only [AlgEquiv.coe_toAlgHom] using congrArg
    (fun g : Fin 2 → MvPolynomial (Fin 4) K => C (2 : K)⁻¹ * aeval g f) hg

/-- The actual reversed pullback word for the alpha-only shear. -/
noncomputable def alphaOnlyFactorization4 (f : MvPolynomial (Fin 2) K) :
    MvPolynomial (Fin 4) K ≃ₐ[K] MvPolynomial (Fin 4) K :=
  splitInverseEquiv4 * splitFlowProduct4 f * splitSourceEquiv4

theorem alphaOnlyFactorization4_X (f : MvPolynomial (Fin 2) K) (j : Fin 4) :
    alphaOnlyFactorization4 f (X j) =
      ![X 0 + X 3 * aeval ![invariant4, X 2] f,
        X 1 + X 2 * aeval ![invariant4, X 2] f, X 2, X 3] j := by
  have hC (c : K) : splitInverseEquiv4 (C c) = (C c : MvPolynomial (Fin 4) K) :=
    splitInverseEquiv4.commutes c
  have htwo : splitInverseEquiv4 (2 : MvPolynomial (Fin 4) K) = 2 := map_ofNat _ 2
  simp only [alphaOnlyFactorization4, AlgEquiv.mul_apply, splitSourceEquiv4_X]
  fin_cases j <;>
    simp [map_add, map_sub, map_mul, splitFlowProduct4_X, splitInverseEquiv4_X,
      splitInverseEquiv4_half_value, hC, htwo]
  · change 2 * (C (2 : K)⁻¹ * (X 1 + X 3) -
        C (2 : K)⁻¹ * (X 1 - X 3)) *
        (C (2 : K)⁻¹ * aeval ![invariant4, X 2] f) =
      X 3 * aeval ![invariant4, X 2] f
    linear_combination ((2 * C (2 : K)⁻¹ + 1) * X 3 * aeval ![invariant4, X 2] f) *
      (two_mul_half_coefficient4 (K := K))
  · change C (2 : K)⁻¹ * (X 1 + X 3) +
        X 2 * (C (2 : K)⁻¹ * aeval ![invariant4, X 2] f) +
        (C (2 : K)⁻¹ * (X 1 - X 3) +
          X 2 * (C (2 : K)⁻¹ * aeval ![invariant4, X 2] f)) =
      X 1 + X 2 * aeval ![invariant4, X 2] f
    linear_combination (X 1 + X 2 * aeval ![invariant4, X 2] f) *
      (two_mul_half_coefficient4 (K := K))
  · linear_combination X (3 : Fin 4) * (two_mul_half_coefficient4 (K := K))

/-- The first case of Lemma 6.2: every polynomial parameter in
`K[Δ,α]` has an explicit tame factorization over the original field. -/
theorem automorphism4_alpha_only_tame (f : MvPolynomial (Fin 2) K) :
    automorphism4 (aeval ![X 0, X 1] f) ∈ Tame.subgroup K 4 := by
  have heq : automorphism4 (aeval ![X 0, X 1] f) = alphaOnlyFactorization4 f := by
    apply AlgEquiv.coe_toAlgHom_injective
    apply MvPolynomial.algHom_ext
    intro j
    change automorphism4 (aeval ![X 0, X 1] f) (X j) = alphaOnlyFactorization4 f (X j)
    rw [automorphism4_X, alphaOnlyFactorization4_X, alpha_only_parameter4]
  rw [heq]
  exact (Tame.subgroup K 4).mul_mem
    ((Tame.subgroup K 4).mul_mem
      (matrixPolynomialCoordinateEquiv_tame _ _ _ _) (splitFlowProduct4_tame f))
    (matrixPolynomialCoordinateEquiv_tame _ _ _ _)

end DimensionFourDependence.DeterminantShear
