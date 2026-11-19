import DimensionFourDependence.SplitQuadraticShearFlows
import DimensionFourDependence.DeterminantShearFamily

/-! # The exact two-flow product and its original constant coordinates -/

namespace DimensionFourDependence.DeterminantShear

open Matrix MvPolynomial

set_option maxHeartbeats 3000000

variable {K : Type*} [Field K] [CharZero K]

noncomputable def splitFlowProduct4 (f : MvPolynomial (Fin 2) K) :
    MvPolynomial (Fin 4) K ≃ₐ[K] MvPolynomial (Fin 4) K :=
  minusFlow4 f * QuadraticFlow.automorphism4 (plusFlowParameter3 f)

/-- The two invariant-parameter quadratic flows cancel their quadratic
corrections and give the shear in the split coordinates. -/
theorem splitFlowProduct4_X (f : MvPolynomial (Fin 2) K) (j : Fin 4) :
    splitFlowProduct4 f (X j) =
      ![X 0 + 2 * (X 1 - X 2) * splitHalfValue4 f,
        X 1 + X 3 * splitHalfValue4 f, X 2 + X 3 * splitHalfValue4 f, X 3] j := by
  have htwo : minusFlow4 f (2 : MvPolynomial (Fin 4) K) = 2 := map_ofNat _ 2
  simp only [splitFlowProduct4, AlgEquiv.mul_apply, QuadraticFlow.automorphism4_X,
    plusFlowParameter3_value]
  fin_cases j <;>
    simp [map_add, map_mul, map_pow, minusFlow4_X, minusFlow4_half_value, htwo] <;> ring

theorem splitFlowProduct4_tame (f : MvPolynomial (Fin 2) K) :
    splitFlowProduct4 f ∈ Tame.subgroup K 4 :=
  (Tame.subgroup K 4).mul_mem (minusFlow4_tame f) (QuadraticFlow.automorphism4_tame _)

/-- The point substitution `(r,s,α,β)=(r,v+u,α,v-u)`. -/
noncomputable def splitSourceMatrix4 : Matrix (Fin 4) (Fin 4) K :=
  ![![1, 0, 0, 0], ![0, 1, 1, 0], ![0, 0, 0, 1], ![0, 1, -1, 0]]

/-- The actual original-field inverse, with `v=(s+β)/2`, `u=(s-β)/2`. -/
noncomputable def splitInverseMatrix4 : Matrix (Fin 4) (Fin 4) K :=
  ![![1, 0, 0, 0], ![0, (2 : K)⁻¹, 0, (2 : K)⁻¹],
    ![0, (2 : K)⁻¹, 0, -(2 : K)⁻¹], ![0, 0, 1, 0]]

theorem splitSourceMatrix4_mul_inverse :
    splitSourceMatrix4 (K := K) * splitInverseMatrix4 = 1 := by
  ext i j
  change (∑ k, splitSourceMatrix4 i k * splitInverseMatrix4 k j) = if i = j then 1 else 0
  fin_cases i <;> fin_cases j <;>
    simp [splitSourceMatrix4, splitInverseMatrix4, Fin.sum_univ_succ] <;> field_simp <;> ring

theorem splitInverseMatrix4_mul_source :
    splitInverseMatrix4 (K := K) * splitSourceMatrix4 = 1 := by
  ext i j
  change (∑ k, splitInverseMatrix4 i k * splitSourceMatrix4 k j) = if i = j then 1 else 0
  fin_cases i <;> fin_cases j <;>
    simp [splitSourceMatrix4, splitInverseMatrix4, Fin.sum_univ_succ] <;> field_simp <;> ring

noncomputable def splitSourceEquiv4 :
    MvPolynomial (Fin 4) K ≃ₐ[K] MvPolynomial (Fin 4) K :=
  matrixPolynomialCoordinateEquiv splitSourceMatrix4 splitInverseMatrix4
    splitSourceMatrix4_mul_inverse splitInverseMatrix4_mul_source

noncomputable def splitInverseEquiv4 :
    MvPolynomial (Fin 4) K ≃ₐ[K] MvPolynomial (Fin 4) K :=
  matrixPolynomialCoordinateEquiv splitInverseMatrix4 splitSourceMatrix4
    splitInverseMatrix4_mul_source splitSourceMatrix4_mul_inverse

theorem splitSourceEquiv4_X (j : Fin 4) :
    splitSourceEquiv4 (X j : MvPolynomial (Fin 4) K) = ![X 0, X 1 + X 2, X 3, X 1 - X 2] j := by
  rw [splitSourceEquiv4, matrixPolynomialCoordinateEquiv_apply]
  simp only [linearPolynomialPullback, aeval_X]
  fin_cases j <;> simp [linearPolynomialMap, splitSourceMatrix4, Fin.sum_univ_succ, sub_eq_add_neg]

theorem splitInverseEquiv4_X (j : Fin 4) :
    splitInverseEquiv4 (X j : MvPolynomial (Fin 4) K) =
      ![X 0, C (2 : K)⁻¹ * (X 1 + X 3), C (2 : K)⁻¹ * (X 1 - X 3), X 2] j := by
  rw [splitInverseEquiv4, matrixPolynomialCoordinateEquiv_apply]
  simp only [linearPolynomialPullback, aeval_X]
  fin_cases j <;> simp [linearPolynomialMap, splitInverseMatrix4,
    Fin.sum_univ_succ, map_neg, mul_add, mul_sub] <;> ring

theorem two_mul_half_coefficient4 :
    (2 : MvPolynomial (Fin 4) K) * C (2 : K)⁻¹ = 1 := by
  rw [show (2 : MvPolynomial (Fin 4) K) = C (2 : K) by simp [map_ofNat],
    ← map_mul, mul_inv_cancel₀ (by norm_num : (2 : K) ≠ 0), map_one]

theorem splitInverseEquiv4_invariant :
    splitInverseEquiv4 (splitInvariant4 : MvPolynomial (Fin 4) K) = invariant4 := by
  simp only [splitInvariant4, QuadraticFlow.quadratic4, map_add, map_sub,
    map_mul, map_pow, splitInverseEquiv4_X]
  have h := two_mul_half_coefficient4 (K := K)
  change X 2 * X 0 - (C (2 : K)⁻¹ * (X 1 + X 3)) ^ 2 +
    (C (2 : K)⁻¹ * (X 1 - X 3)) ^ 2 = X 2 * X 0 - X 3 * X 1
  linear_combination -(C (2 : K)⁻¹ * (X 1 * X 3 * 2)) * h - X 1 * X 3 * h

end DimensionFourDependence.DeterminantShear
