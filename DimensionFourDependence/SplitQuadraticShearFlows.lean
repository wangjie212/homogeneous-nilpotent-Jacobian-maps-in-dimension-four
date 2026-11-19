import DimensionFourDependence.QuadraticFlowTameness
import DimensionFourDependence.LinearTameConjugacy

/-! # The two tame quadratic flows in equation (6.3) -/

namespace DimensionFourDependence.DeterminantShear

open Matrix MvPolynomial

set_option maxHeartbeats 3000000

variable {K : Type*} [Field K]

noncomputable def reflectionSwapMatrix4 : Matrix (Fin 4) (Fin 4) K :=
  ![![-1, 0, 0, 0], ![0, 0, 1, 0], ![0, 1, 0, 0], ![0, 0, 0, 1]]

theorem reflectionSwapMatrix4_square :
    reflectionSwapMatrix4 (K := K) * reflectionSwapMatrix4 = 1 := by
  ext i j
  change (∑ k, reflectionSwapMatrix4 i k * reflectionSwapMatrix4 k j) = if i = j then 1 else 0
  fin_cases i <;> fin_cases j <;>
    simp [reflectionSwapMatrix4, Matrix.mul_apply, Fin.sum_univ_succ]

noncomputable def reflectionSwapEquiv4 :
    MvPolynomial (Fin 4) K ≃ₐ[K] MvPolynomial (Fin 4) K :=
  matrixPolynomialCoordinateEquiv reflectionSwapMatrix4 reflectionSwapMatrix4
    reflectionSwapMatrix4_square reflectionSwapMatrix4_square

theorem reflectionSwapEquiv4_X (j : Fin 4) :
    reflectionSwapEquiv4 (X j : MvPolynomial (Fin 4) K) = ![-X 0, X 2, X 1, X 3] j := by
  rw [reflectionSwapEquiv4, matrixPolynomialCoordinateEquiv_apply]
  simp only [linearPolynomialPullback, aeval_X]
  fin_cases j <;> simp [linearPolynomialMap, reflectionSwapMatrix4, Fin.sum_univ_succ]

theorem reflectionSwapEquiv4_C (c : K) :
    reflectionSwapEquiv4 (C c : MvPolynomial (Fin 4) K) = C c := reflectionSwapEquiv4.commutes c

theorem reflectionSwapEquiv4_tame : reflectionSwapEquiv4 (K := K) ∈ Tame.subgroup K 4 :=
  matrixPolynomialCoordinateEquiv_tame _ _ _ _

noncomputable def splitInvariant4 : MvPolynomial (Fin 4) K :=
  QuadraticFlow.quadratic4 + X 2 ^ 2

noncomputable def splitHalfValue4 (f : MvPolynomial (Fin 2) K) : MvPolynomial (Fin 4) K :=
  C (2 : K)⁻¹ * aeval ![splitInvariant4, X 3] f

noncomputable def plusFlowParameter3 (f : MvPolynomial (Fin 2) K) : MvPolynomial (Fin 3) K :=
  C (2 : K)⁻¹ * aeval ![X 0 + X 1 ^ 2, X 2] f

noncomputable def minusFlowParameter3 (f : MvPolynomial (Fin 2) K) : MvPolynomial (Fin 3) K :=
  C (2 : K)⁻¹ * aeval ![-X 0 - X 1 ^ 2, X 2] f

theorem plusFlowParameter3_value (f : MvPolynomial (Fin 2) K) :
    QuadraticFlow.parameter4 (plusFlowParameter3 f) = splitHalfValue4 f := by
  unfold QuadraticFlow.parameter4 plusFlowParameter3 splitHalfValue4
  rw [map_mul, aeval_C, algebraMap_eq, comp_aeval_apply]
  have hg : (fun i : Fin 2 =>
      (aeval (![QuadraticFlow.quadratic4, X 2, X 3] : Fin 3 → MvPolynomial (Fin 4) K))
        ((![X 0 + X 1 ^ 2, X 2] : Fin 2 → MvPolynomial (Fin 3) K) i)) =
      ![splitInvariant4, X 3] := by
    funext i
    fin_cases i <;> simp [splitInvariant4]
  rw [hg]

theorem minusFlowParameter3_reflected_value (f : MvPolynomial (Fin 2) K) :
    reflectionSwapEquiv4 (QuadraticFlow.parameter4 (minusFlowParameter3 f)) = splitHalfValue4 f := by
  unfold QuadraticFlow.parameter4 minusFlowParameter3
  rw [map_mul, aeval_C, algebraMap_eq, map_mul, reflectionSwapEquiv4_C, comp_aeval_apply]
  change C (2 : K)⁻¹ * reflectionSwapEquiv4.toAlgHom (aeval _ f) = _
  rw [Tame.algHom_aeval]
  have hg : (fun i : Fin 2 => reflectionSwapEquiv4
      ((aeval (![QuadraticFlow.quadratic4, X 2, X 3] : Fin 3 → MvPolynomial (Fin 4) K))
        ((![-X 0 - X 1 ^ 2, X 2] : Fin 2 → MvPolynomial (Fin 3) K) i))) =
      ![splitInvariant4, X 3] := by
    funext i
    fin_cases i <;> simp [QuadraticFlow.quadratic4, splitInvariant4,
      reflectionSwapEquiv4_X] <;> ring
  simpa only [splitHalfValue4, AlgEquiv.coe_toAlgHom] using
    congrArg (fun g : Fin 2 → MvPolynomial (Fin 4) K => C (2 : K)⁻¹ * aeval g f) hg

/-- The flow of `-2u∂r+α∂u`, obtained from the already constructed
quadratic flow by an actual original-field linear involution. -/
noncomputable def minusFlow4 (f : MvPolynomial (Fin 2) K) :
    MvPolynomial (Fin 4) K ≃ₐ[K] MvPolynomial (Fin 4) K :=
  reflectionSwapEquiv4 * QuadraticFlow.automorphism4 (minusFlowParameter3 f) * reflectionSwapEquiv4

theorem minusFlow4_X (f : MvPolynomial (Fin 2) K) (j : Fin 4) :
    minusFlow4 f (X j) =
      ![X 0 - 2 * X 2 * splitHalfValue4 f - X 3 * splitHalfValue4 f ^ 2,
        X 1, X 2 + X 3 * splitHalfValue4 f, X 3] j := by
  have htwo : reflectionSwapEquiv4 (2 : MvPolynomial (Fin 4) K) = 2 := map_ofNat _ 2
  fin_cases j <;>
    simp [minusFlow4, AlgEquiv.mul_apply, reflectionSwapEquiv4_X,
      QuadraticFlow.automorphism4_X, minusFlowParameter3_reflected_value,
      map_add, map_sub, map_mul, map_pow, map_neg, htwo] <;> ring

theorem minusFlow4_invariant (f : MvPolynomial (Fin 2) K) :
    minusFlow4 f splitInvariant4 = splitInvariant4 := by
  simp [splitInvariant4, QuadraticFlow.quadratic4, minusFlow4_X]
  ring

theorem minusFlow4_half_value (f g : MvPolynomial (Fin 2) K) :
    minusFlow4 f (splitHalfValue4 g) = splitHalfValue4 g := by
  have hC (c : K) : minusFlow4 f (C c) = C c := (minusFlow4 f).commutes c
  rw [splitHalfValue4, map_mul, hC]
  change C (2 : K)⁻¹ * (minusFlow4 f).toAlgHom (aeval ![splitInvariant4, X 3] g) = _
  rw [Tame.algHom_aeval]
  have hg : (fun i : Fin 2 => minusFlow4 f (![splitInvariant4, X 3] i)) =
      ![splitInvariant4, X 3] := by
    funext i
    fin_cases i <;> simp [minusFlow4_invariant, minusFlow4_X]
  simpa only [splitHalfValue4, AlgEquiv.coe_toAlgHom] using
    congrArg (fun x : Fin 2 → MvPolynomial (Fin 4) K => C (2 : K)⁻¹ * aeval x g) hg

variable [CharZero K]

theorem minusFlow4_tame (f : MvPolynomial (Fin 2) K) :
    minusFlow4 f ∈ Tame.subgroup K 4 :=
  (Tame.subgroup K 4).mul_mem
    ((Tame.subgroup K 4).mul_mem reflectionSwapEquiv4_tame (QuadraticFlow.automorphism4_tame _))
    reflectionSwapEquiv4_tame

end DimensionFourDependence.DeterminantShear
