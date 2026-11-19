import DimensionFourDependence.TernaryQuadraticRelationTransport

/-! # Exact output formulas from a normalizer with fixed outer coordinates -/

namespace DimensionFourDependence

open MvPolynomial Matrix

universe u
set_option maxHeartbeats 4100000

variable {K : Type u} [Field K]
local notation "R₃" => MvPolynomial (Fin 3) K
local notation "M₃" => Matrix (Fin 3) (Fin 3) K

/-- When the outer rows of the normalizer are diagonal with compatible
scales, the original polynomial outputs have three explicit scalar
coefficients and a common ordinary polynomial in the displayed argument. -/
theorem ternary_outer_normalizer_constructs_original_output_formulas
    (G : Fin 3 → R₃) (T S : M₃) (hTS : T * S = 1)
    (P : Polynomial K) (hP : 0 < P.natDegree) (hP₀ : P.eval 0 = 0)
    (he : linearPolynomialConjugate T S G = TernaryNormalForm.perturbation3 P)
    (t : K) (ht : t ≠ 0)
    (h₀ : ∀ i, S 0 i = if i = 0 then t else 0)
    (h₂ : ∀ i, S 2 i = if i = 2 then t ^ 2 else 0) :
    ∃ (lam b d : K) (Q : Polynomial K), lam ≠ 0 ∧ 0 < Q.natDegree ∧ Q.eval 0 = 0 ∧
      G 0 = Polynomial.aeval (X 1 + C b * X 0 + C d * X 2 + C lam * X 0 ^ 2) Q ∧
      G 1 = C lam * (X 2 - 2 * X 0 * G 0) - C b * G 0 - C d * (G 0) ^ 2 ∧ G 2 = (G 0) ^ 2 := by
  let l := S 1 0
  let c := S 1 1
  let m := S 1 2
  have ht₂ : t ^ 2 ≠ 0 := pow_ne_zero _ ht
  have hS : S.det ≠ 0 := by
    have hz := congrArg Matrix.det hTS
    rw [Matrix.det_mul, Matrix.det_one] at hz
    intro h
    rw [h, mul_zero] at hz
    exact zero_ne_one hz
  have hc : c ≠ 0 := by
    intro h
    apply hS
    rw [Matrix.det_fin_three]
    simp [h₀, h₂, show S 1 1 = 0 from h]
  let lam := t ^ 2 / c
  let b := l / c
  let d := m / c
  let q := Polynomial.C c * Polynomial.X
  let Q := Polynomial.C t⁻¹ * P.comp q
  let R : R₃ := X 1 + C b * X 0 + C d * X 2 + C lam * X 0 ^ 2
  let Y : R₃ := C l * X 0 + C c * X 1 + C m * X 2
  let A := Polynomial.aeval (X 1 + (X 0 : R₃) ^ 2) P
  let e : R₃ →ₐ[K] R₃ := aeval (linearPolynomialMap S)
  have he₀ : e (X (0 : Fin 3)) = C t * X 0 := by
    rw [show e (X (0 : Fin 3)) = linearPolynomialMap S 0 from aeval_X _ _]
    simp [linearPolynomialMap, Fin.sum_univ_three, h₀]
  have he₁ : e (X (1 : Fin 3)) = Y := by
    rw [show e (X (1 : Fin 3)) = linearPolynomialMap S 1 from aeval_X _ _]
    exact Fin.sum_univ_three _
  have he₂ : e (X (2 : Fin 3)) = C (t ^ 2) * X 2 := by
    rw [show e (X (2 : Fin 3)) = linearPolynomialMap S 2 from aeval_X _ _]
    simp [linearPolynomialMap, Fin.sum_univ_three, h₂]
  have hOut := ternary_normalizing_matrix_output_identity G T S hTS P he
  have hA : C t * G 0 = e A := by
    have hh := congrFun hOut 0
    change (∑ i, C (S 0 i) * G i) = e A at hh
    simpa [Fin.sum_univ_three, h₀] using hh
  have hV : C l * G 0 + C c * G 1 + C m * G 2 = e (X 2 - 2 * X 0 * A) := by
    have hh := congrFun hOut 1
    change (∑ i, C (S 1 i) * G i) = e (X 2 - 2 * X 0 * A) at hh
    rwa [Fin.sum_univ_three] at hh
  have hW : C (t ^ 2) * G 2 = (e A) ^ 2 := by
    have hh := congrFun hOut 2
    change (∑ i, C (S 2 i) * G i) = e (A ^ 2) at hh
    simpa [Fin.sum_univ_three, h₂, map_pow] using hh
  have hSq : G 2 = (G 0) ^ 2 := by
    apply mul_left_cancel₀ (MvPolynomial.C_ne_zero.mpr ht₂ : C (t ^ 2) ≠ (0 : R₃))
    rw [hW, ← hA, mul_pow, map_pow]
  have hbc : C c * C b = (C l : R₃) := by rw [← map_mul]; exact congrArg C (mul_div_cancel₀ _ hc)
  have hdc : C c * C d = (C m : R₃) := by rw [← map_mul]; exact congrArg C (mul_div_cancel₀ _ hc)
  have hlamc : C c * C lam = (C (t ^ 2) : R₃) := by rw [← map_mul]; exact congrArg C (mul_div_cancel₀ _ hc)
  have hScale : Y + (C t * X 0) ^ 2 = C c * R := by
    dsimp only [Y, R]
    rw [map_pow] at hlamc
    linear_combination -X (0 : Fin 3) * hbc - X 2 * hdc - X 0 ^ 2 * hlamc
  have hQt : C t * Polynomial.aeval R Q = e A := by
    change _ = e (Polynomial.aeval (X 1 + (X 0 : R₃) ^ 2) P)
    rw [← Polynomial.aeval_algHom_apply, map_add, map_pow, he₀, he₁, hScale]
    have hR : Polynomial.aeval R q = C c * R := by
      simp only [q, map_mul, Polynomial.aeval_C, Polynomial.aeval_X, algebraMap_eq]
    dsimp only [Q]
    rw [map_mul, Polynomial.aeval_C, algebraMap_eq, Polynomial.aeval_comp, hR,
      ← mul_assoc, ← map_mul, mul_inv_cancel₀ ht, map_one, one_mul]
  have hG : G 0 = Polynomial.aeval R Q :=
    mul_left_cancel₀ (MvPolynomial.C_ne_zero.mpr ht) (hA.trans hQt.symm)
  have hG₁ : G 1 = C lam * (X 2 - 2 * X 0 * G 0) - C b * G 0 - C d * (G 0) ^ 2 := by
    apply mul_left_cancel₀ (MvPolynomial.C_ne_zero.mpr hc : C c ≠ (0 : R₃))
    rw [hSq] at hV
    simp only [map_sub, map_mul, map_ofNat, he₂, he₀, ← hA, map_pow] at hV
    rw [map_pow] at hlamc
    linear_combination hV - (X 2 - 2 * X 0 * G 0) * hlamc + G 0 * hbc + (G 0) ^ 2 * hdc
  have hQ : 0 < Q.natDegree := by
    change 0 < (Polynomial.C t⁻¹ * P.comp q).natDegree
    rw [Polynomial.natDegree_C_mul (inv_ne_zero ht), Polynomial.natDegree_comp,
      show q.natDegree = 1 from Polynomial.natDegree_C_mul_X c hc, mul_one]
    exact hP
  exact ⟨lam, b, d, Q, div_ne_zero ht₂ hc, hQ, by simp [Q, q, hP₀], hG, hG₁, hSq⟩

end DimensionFourDependence
