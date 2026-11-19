import DimensionFourDependence.TernaryClassificationSpecification
import Mathlib.Algebra.Polynomial.Degree.Lemmas

/-! # An original parabolic formula gives the exact original normalizer -/

namespace DimensionFourDependence

open MvPolynomial Matrix

universe u
set_option maxHeartbeats 4100000

variable {K : Type u} [Field K]
local notation "R₃" => MvPolynomial (Fin 3) K
local notation "M₃" => Matrix (Fin 3) (Fin 3) K

/-- Once the parabolic formulas have original coefficients, a single
specified original shear and scaling give the canonical perturbation. -/
theorem ternary_parabolic_output_formula_conjugates_to_normal_form
    (G : Fin 3 → R₃) (lam b d : K) (hlam : lam ≠ 0) (Q : Polynomial K)
    (hQ : 0 < Q.natDegree) (hQ₀ : Q.eval 0 = 0)
    (h₀ : G 0 = Polynomial.aeval (X 1 + C b * X 0 + C d * X 2 + C lam * X 0 ^ 2) Q)
    (h₁ : G 1 = C lam * (X 2 - 2 * X 0 * G 0) - C b * G 0 - C d * (G 0) ^ 2)
    (h₂ : G 2 = (G 0) ^ 2) :
    ∃ (T S : M₃) (P : Polynomial K), T * S = 1 ∧ S * T = 1 ∧
      0 < P.natDegree ∧ P.eval 0 = 0 ∧ linearPolynomialConjugate T S G = TernaryNormalForm.perturbation3 P := by
  let S : M₃ := of ![![1, 0, 0], ![lam⁻¹ * b, lam⁻¹, lam⁻¹ * d], ![0, 0, 1]]
  let T := S⁻¹
  have hdet : S.det = lam⁻¹ := by
    rw [Matrix.det_fin_three]
    change (1 : K) * lam⁻¹ * 1 - 1 * (lam⁻¹ * d) * 0 - 0 * (lam⁻¹ * b) * 1 +
      0 * (lam⁻¹ * d) * 0 + 0 * (lam⁻¹ * b) * 0 - 0 * lam⁻¹ * 0 = _
    ring
  have hS : IsUnit S.det := isUnit_iff_ne_zero.mpr (hdet.symm ▸ inv_ne_zero hlam)
  have hTS : T * S = 1 := Matrix.nonsing_inv_mul S hS
  have hST : S * T = 1 := Matrix.mul_nonsing_inv S hS
  let A : R₃ := X 1 + C b * X 0 + C d * X 2 + C lam * X 0 ^ 2
  let q : Polynomial K := Polynomial.C lam * Polynomial.X
  let P := Q.comp q
  let L := linearPolynomialMap S
  let e : R₃ →ₐ[K] R₃ := aeval L
  let U := Polynomial.aeval (X 1 + (X 0 : R₃) ^ 2) P
  have hQ' : 0 < P.natDegree := by
    change 0 < (Q.comp q).natDegree
    rw [Polynomial.natDegree_comp, show q.natDegree = 1 from Polynomial.natDegree_C_mul_X lam hlam, mul_one]
    exact hQ
  have hQ₀' : P.eval 0 = 0 := by simp [P, q, hQ₀]
  have hL₀ : e (X 0) = X 0 := by
    rw [aeval_X]
    change (∑ j, C (S 0 j) * X j) = X 0
    rw [Fin.sum_univ_three]
    change C (1 : K) * X 0 + C (0 : K) * X 1 + C (0 : K) * X 2 = _
    simp
  have hL₂ : e (X 2) = X 2 := by
    rw [aeval_X]
    change (∑ j, C (S 2 j) * X j) = X 2
    rw [Fin.sum_univ_three]
    change C (0 : K) * X 0 + C (0 : K) * X 1 + C (1 : K) * X 2 = _
    simp
  have hL₁ : e (X 1) = C lam⁻¹ * (X 1 + C b * X 0 + C d * X 2) := by
    rw [aeval_X]
    change (∑ j, C (S 1 j) * X j) = _
    rw [Fin.sum_univ_three]
    change C (lam⁻¹ * b) * X 0 + C lam⁻¹ * X 1 + C (lam⁻¹ * d) * X 2 = _
    simp only [map_mul]
    ring
  have hlam₁ : C lam * C lam⁻¹ = (1 : R₃) := by rw [← map_mul, mul_inv_cancel₀ hlam, map_one]
  have hA : C lam * (e (X 1) + (e (X 0)) ^ 2) = A := by
    rw [hL₁, hL₀]
    dsimp only [A]
    linear_combination (X 1 + C b * X 0 + C d * X 2) * hlam₁
  have hU : e U = G 0 := by
    change e (Polynomial.aeval (X 1 + (X 0 : R₃) ^ 2) (Q.comp q)) = _
    rw [← Polynomial.aeval_algHom_apply, map_add, map_pow, Polynomial.aeval_comp]
    have heq : Polynomial.aeval (e (X 1) + e (X 0) ^ 2) q = A := by
      simpa only [q, map_mul, Polynomial.aeval_C, Polynomial.aeval_X, algebraMap_eq] using hA
    rw [heq]
    exact h₀.symm
  have hPush (i : Fin 3) : ∑ j, C (S i j) * G j = e (TernaryNormalForm.perturbation3 P i) := by
    rw [Fin.sum_univ_three]
    fin_cases i
    · change C (1 : K) * G 0 + C (0 : K) * G 1 + C (0 : K) * G 2 = e U
      rw [hU]; simp
    · change C (lam⁻¹ * b) * G 0 + C lam⁻¹ * G 1 + C (lam⁻¹ * d) * G 2 = e (X 2 - 2 * X 0 * U)
      rw [h₁, h₂]
      simp only [map_mul, map_sub, map_ofNat, hL₂, hL₀, hU]
      linear_combination (X 2 - 2 * X 0 * G 0) * hlam₁
    · change C (0 : K) * G 0 + C (0 : K) * G 1 + C (1 : K) * G 2 = e (U ^ 2)
      rw [map_pow, hU, h₂]; simp
  refine ⟨T, S, P, hTS, hST, hQ', hQ₀', ?_⟩
  funext i
  calc
    linearPolynomialConjugate T S G i = linearPolynomialPullback T (∑ j, C (S i j) * G j) := by
      simp only [linearPolynomialConjugate, linearPolynomialPullback, map_sum, map_mul, aeval_C, algebraMap_eq]
    _ = TernaryNormalForm.perturbation3 P i := by
      rw [hPush i]
      exact matrix_linear_polynomial_substitution_inverse S T hST _

end DimensionFourDependence
