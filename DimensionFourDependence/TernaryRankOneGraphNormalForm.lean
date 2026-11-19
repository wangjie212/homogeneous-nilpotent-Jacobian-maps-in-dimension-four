import DimensionFourDependence.TernaryClassificationSpecification
import DimensionFourDependence.TernaryBinaryQuadraticRank

/-! # The original constant conjugacy of a rank-one quadratic graph -/

namespace DimensionFourDependence

open MvPolynomial Matrix

universe u
set_option maxHeartbeats 4400000

variable {K : Type u} [Field K] [CharZero K]
local notation "R₃" => MvPolynomial (Fin 3) K

/-- A nonzero rank-one quadratic graph with independent transverse
linear remainder is the canonical ternary perturbation after one
explicit constant conjugacy in the original source coordinates. -/
theorem ternary_rank_one_graph_conjugates_to_normal_form
    (H : Fin 3 → R₃) (k u v l m a b : K) (hk : k ≠ 0) (hdet : u * b - v * a ≠ 0)
    (f g : Polynomial K) (hf : f.eval 0 = 0) (hg : g.eval 0 = 0)
    (hp : 0 < (Polynomial.C u * f + Polynomial.C v * g).natDegree)
    (hrel : Polynomial.C k * (Polynomial.C u * f + Polynomial.C v * g) ^ 2 +
      Polynomial.C a * f + Polynomial.C b * g = 0)
    (hChart :
      let L : R₃ := C u * X 0 + C v * X 2
      let ρ : R₃ := X 1 - (C l * X 0 + C m * X 2) - C k * L ^ 2
      let F := Polynomial.aeval ρ f
      let G := Polynomial.aeval ρ g
      H 0 = F ∧ H 2 = G ∧ H 1 = C l * F + C m * G +
        2 * C k * L * (C u * F + C v * G) + (C a * X 0 + C b * X 2)) :
    ∃ (T S : Matrix (Fin 3) (Fin 3) K) (P : Polynomial K), T * S = 1 ∧ S * T = 1 ∧
      0 < P.natDegree ∧ P.eval 0 = 0 ∧ linearPolynomialConjugate T S H = TernaryNormalForm.perturbation3 P := by
  let L : R₃ := C u * X 0 + C v * X 2
  let B : R₃ := C l * X 0 + C m * X 2
  let W : R₃ := C a * X 0 + C b * X 2
  let ρ : R₃ := X 1 - B - C k * L ^ 2
  let p := Polynomial.C u * f + Polynomial.C v * g
  let F := Polynomial.aeval ρ f
  let G := Polynomial.aeval ρ g
  let A := C u * F + C v * G
  let q : Polynomial K := Polynomial.C (-k) * Polynomial.X
  let P := p.comp q
  have hP : 0 < P.natDegree := by
    change 0 < (p.comp q).natDegree
    rw [Polynomial.natDegree_comp, show q.natDegree = 1 from
      Polynomial.natDegree_C_mul_X _ (neg_ne_zero.mpr hk), mul_one]
    exact hp
  have hP₀ : P.eval 0 = 0 := by simp [P, p, q, hf, hg]
  let S : Matrix (Fin 3) (Fin 3) K := of ![![u, 0, v], ![l * k⁻¹, -k⁻¹, m * k⁻¹], ![-(a * k⁻¹), 0, -(b * k⁻¹)]]
  have hS : S.det = (k⁻¹ * k⁻¹) * (u * b - v * a) := by
    rw [Matrix.det_fin_three]
    change u * -k⁻¹ * -(b * k⁻¹) - u * (m * k⁻¹) * 0 -
      0 * (l * k⁻¹) * -(b * k⁻¹) + 0 * (m * k⁻¹) * -(a * k⁻¹) +
      v * (l * k⁻¹) * 0 - v * -k⁻¹ * -(a * k⁻¹) = _
    ring
  have hUnit : IsUnit S.det := isUnit_iff_ne_zero.mpr (hS.symm ▸ mul_ne_zero (mul_ne_zero (inv_ne_zero hk) (inv_ne_zero hk)) hdet)
  let T := S⁻¹
  have hTS : T * S = 1 := Matrix.nonsing_inv_mul S hUnit
  have hST : S * T = 1 := Matrix.mul_nonsing_inv S hUnit
  let Lₛ := linearPolynomialMap S
  have h₀ : Lₛ 0 = L := by
    change (∑ j, C (S 0 j) * X j) = L
    rw [Fin.sum_univ_three]
    change C u * X 0 + C (0 : K) * X 1 + C v * X 2 = L
    simp [L]
  have h₁ : Lₛ 1 = -C k⁻¹ * (X 1 - B) := by
    change (∑ j, C (S 1 j) * X j) = _
    rw [Fin.sum_univ_three]
    change C (l * k⁻¹) * X 0 + C (-k⁻¹) * X 1 + C (m * k⁻¹) * X 2 = _
    simp only [B, map_mul, map_neg]
    ring
  have h₂ : Lₛ 2 = -C k⁻¹ * W := by
    change (∑ j, C (S 2 j) * X j) = _
    rw [Fin.sum_univ_three]
    change C (-(a * k⁻¹)) * X 0 + C (0 : K) * X 1 + C (-(b * k⁻¹)) * X 2 = _
    simp only [W, map_neg, map_mul, map_zero, zero_mul, add_zero]
    ring
  have hk₁ : C k⁻¹ * C k = (1 : R₃) := by rw [← map_mul, inv_mul_cancel₀ hk, map_one]
  have hρ : C (-k) * (Lₛ 1 + Lₛ 0 ^ 2) = ρ := by
    rw [h₁, h₀, map_neg]
    dsimp only [ρ]
    linear_combination (X (1 : Fin 3) - B) * hk₁
  let U := Polynomial.aeval (X 1 + (X 0 : R₃) ^ 2) P
  have hU : aeval Lₛ U = A := by
    change aeval Lₛ (Polynomial.aeval (X 1 + (X 0 : R₃) ^ 2) (p.comp q)) = _
    rw [← Polynomial.aeval_algHom_apply, map_add, map_pow, aeval_X, aeval_X, Polynomial.aeval_comp]
    have hq : Polynomial.aeval (Lₛ 1 + Lₛ 0 ^ 2) q = ρ := by
      simpa only [q, map_mul, Polynomial.aeval_C, Polynomial.aeval_X, algebraMap_eq] using hρ
    rw [hq]
    simp only [p, A, F, G, map_add, map_mul, Polynomial.aeval_C, algebraMap_eq]
  have hRel : C k * A ^ 2 + C a * F + C b * G = 0 := by
    simpa only [A, p, F, G, map_add, map_mul, map_pow, map_zero, Polynomial.aeval_C, algebraMap_eq] using
      congrArg (Polynomial.aeval ρ) hrel
  obtain ⟨hF, hG, hV⟩ := hChart
  change H 0 = F at hF
  change H 2 = G at hG
  change H 1 = C l * F + C m * G + 2 * C k * L * A + W at hV
  have hPush (i : Fin 3) : ∑ j, C (S i j) * H j = aeval Lₛ (TernaryNormalForm.perturbation3 P i) := by
    rw [Fin.sum_univ_three]
    fin_cases i
    · change C u * H 0 + C (0 : K) * H 1 + C v * H 2 = aeval Lₛ U
      rw [hF, hG, hU, map_zero, zero_mul, add_zero]
    · change C (l * k⁻¹) * H 0 + C (-k⁻¹) * H 1 + C (m * k⁻¹) * H 2 =
        aeval Lₛ (X 2 - 2 * X 0 * U)
      rw [hF, hG, hV]
      simp only [map_mul, map_neg, map_sub, aeval_X, map_ofNat, h₂, h₀, hU]
      linear_combination -(2 * L * A) * hk₁
    · change C (-(a * k⁻¹)) * H 0 + C (0 : K) * H 1 + C (-(b * k⁻¹)) * H 2 = aeval Lₛ (U ^ 2)
      rw [hF, hG]
      simp only [map_neg, map_mul, map_zero, zero_mul, add_zero, map_pow, hU]
      linear_combination -C k⁻¹ * hRel + A ^ 2 * hk₁
  refine ⟨T, S, P, hTS, hST, hP, hP₀, ?_⟩
  funext i
  calc
    linearPolynomialConjugate T S H i = linearPolynomialPullback T (∑ j, C (S i j) * H j) := by
      simp only [linearPolynomialConjugate, linearPolynomialPullback, map_sum, map_mul, aeval_C,
        algebraMap_eq]
    _ = TernaryNormalForm.perturbation3 P i := by
      rw [hPush i]
      exact matrix_linear_polynomial_substitution_inverse S T hST _

end DimensionFourDependence
