import DimensionFourDependence.TernaryNormalizationCovectorDescent
import DimensionFourDependence.TernaryOriginalCoefficientMaps

/-! # Scalar and polynomial coefficients of the parabolic chart descend -/

namespace DimensionFourDependence

open MvPolynomial Matrix

universe u
set_option maxHeartbeats 4850000

variable {K E : Type u} [Field K] [Field E] [Algebra K E]
local notation "R₃" => MvPolynomial (Fin 3) K
local notation "Rₑ" => MvPolynomial (Fin 3) E
local notation "j" => (algebraMap K E)
local notation "Rmap" => (MvPolynomial.map (σ := Fin 3) j)

/-- The three polynomials determining the middle output are linearly
independent. Restriction to the middle source axis proves the assertion
for the two positive powers, and the outer coordinate then separates
the remaining polynomial. -/
theorem ternary_parabolic_output_coefficients_unique
    (F : Rₑ) (Q : Polynomial E) (hQ : 0 < Q.natDegree)
    (hAxis : aeval (![0, Polynomial.X, 0] : Fin 3 → Polynomial E) F = Q)
    (a b c : E) (he : C a * (X 2 - 2 * X 0 * F) + C b * F + C c * F ^ 2 = 0) :
    a = 0 ∧ b = 0 ∧ c = 0 := by
  let y : Fin 3 → Polynomial E := ![0, Polynomial.X, 0]
  have hzero : Polynomial.C b * Q + Polynomial.C c * Q ^ 2 = 0 := by
    have h := congrArg (aeval y) he
    change aeval y F = Q at hAxis
    simp only [map_add, map_mul, map_sub, map_pow, map_zero, aeval_C, aeval_X, hAxis, Polynomial.algebraMap_eq] at h
    change Polynomial.C a * (0 - (_ * 0 * Q)) + Polynomial.C b * Q + Polynomial.C c * Q ^ 2 = 0 at h
    simpa only [mul_zero, zero_mul, sub_self, zero_add] using h
  let W : Polynomial E := Polynomial.C b * Polynomial.X + Polynomial.C c * Polynomial.X ^ 2
  have hW : W = 0 := by
    have he : W.comp Q = 0 := by
      simpa only [W, Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp, Polynomial.C_comp,
        Polynomial.X_comp] using hzero
    rcases Polynomial.comp_eq_zero_iff.mp he with h | ⟨_, h⟩
    · exact h
    · have hz := congrArg Polynomial.natDegree h
      rw [Polynomial.natDegree_C] at hz
      omega
  have hc (k : ℕ) : (Polynomial.C b * Polynomial.X).coeff k = if k = 1 then b else 0 := by
    rw [← pow_one (Polynomial.X : Polynomial E), Polynomial.coeff_C_mul_X_pow]
  have hb : b = 0 := by
    have h := congrArg (fun p : Polynomial E => p.coeff 1) hW
    simpa [W, hc, Polynomial.coeff_C_mul_X_pow] using h
  have hC : c = 0 := by
    have h := congrArg (fun p : Polynomial E => p.coeff 2) hW
    simpa [W, hc, Polynomial.coeff_C_mul_X_pow] using h
  rw [hb, hC, map_zero, zero_mul, zero_mul, add_zero, add_zero] at he
  have hA : C a * (X 2 - 2 * X 0 * F) = 0 := he
  rcases mul_eq_zero.mp hA with ha | hz
  · exact ⟨MvPolynomial.C_injective (Fin 3) E (ha.trans (map_zero C).symm), hb, hC⟩
  · let z : Fin 3 → Polynomial E := ![0, 0, Polynomial.X]
    have h := congrArg (aeval z) hz
    simp only [map_sub, map_mul, map_zero, aeval_X] at h
    change Polynomial.X - (_ * 0 * _) = (0 : Polynomial E) at h
    simp at h

/-- All three coefficients and the ordinary polynomial in the
parabolic chart are defined over the original coefficient field. -/
theorem ternary_parabolic_output_formulas_descend
    (G : Fin 3 → R₃) (lam b d : E) (hlam : lam ≠ 0) (Q : Polynomial E)
    (hQ : 0 < Q.natDegree) (hQ₀ : Q.eval 0 = 0)
    (h₀ : Rmap (G 0) = Polynomial.aeval (X 1 + C b * X 0 + C d * X 2 + C lam * X 0 ^ 2) Q)
    (h₁ : Rmap (G 1) = C lam * (X 2 - 2 * X 0 * Rmap (G 0)) - C b * Rmap (G 0) - C d * (Rmap (G 0)) ^ 2)
    (h₂ : Rmap (G 2) = (Rmap (G 0)) ^ 2) :
    ∃ (μ B D : K) (p : Polynomial K), μ ≠ 0 ∧ 0 < p.natDegree ∧ p.eval 0 = 0 ∧
      G 0 = Polynomial.aeval (X 1 + C B * X 0 + C D * X 2 + C μ * X 0 ^ 2) p ∧
      G 1 = C μ * (X 2 - 2 * X 0 * G 0) - C B * G 0 - C D * (G 0) ^ 2 ∧ G 2 = (G 0) ^ 2 := by
  let y₀ : Fin 3 → Polynomial K := ![0, Polynomial.X, 0]
  let y : Fin 3 → Polynomial E := ![0, Polynomial.X, 0]
  let p := aeval y₀ (G 0)
  let F := Rmap (G 0)
  let R : Rₑ := X 1 + C b * X 0 + C d * X 2 + C lam * X 0 ^ 2
  have hr : aeval y R = Polynomial.X := by
    simp only [R, map_add, map_mul, map_pow, aeval_X]
    change Polynomial.X + _ * 0 + _ * 0 + _ * (0 : Polynomial E) ^ 2 = _
    simp
  have hAxis : aeval y F = Q := by
    change F = Polynomial.aeval R Q at h₀
    rw [h₀, ← Polynomial.aeval_algHom_apply, hr, Polynomial.aeval_X_left_apply]
  have hP : p.map j = Q := by
    let φ := Polynomial.mapAlgHom (Algebra.ofId K E)
    have hy : φ ∘ y₀ = y := by funext i; fin_cases i <;> simp [φ, y₀, y]
    change φ (aeval y₀ (G 0)) = _
    rw [polynomial_aeval_scalar_extension (E := E) φ, hy]
    exact hAxis
  have hp : 0 < p.natDegree := by
    rw [← Polynomial.natDegree_map_eq_of_injective (algebraMap K E).injective p, hP]
    exact hQ
  have hp₀ : p.eval 0 = 0 := by
    apply (algebraMap K E).injective
    rw [← Polynomial.eval_map_apply, map_zero, hP, hQ₀]
  obtain ⟨ψ, hψ⟩ : ∃ ψ : E →ₗ[K] K, ψ 1 ≠ 0 := by
    by_contra! h
    exact one_ne_zero ((Module.forall_dual_apply_eq_zero_iff K (1 : E)).mp h)
  let φ := (ψ 1)⁻¹ • ψ
  have hφ : φ 1 = 1 := inv_mul_cancel₀ hψ
  let μ := φ lam
  let B := φ b
  let D := φ d
  let A : Fin 3 → R₃ := ![X 2 - 2 * X 0 * G 0, G 0, (G 0) ^ 2]
  let c : Fin 3 → E := ![lam, -b, -d]
  have hSum : ∑ i, C (c i) * Rmap (A i) = Rmap (G 1) := by
    rw [Fin.sum_univ_three]
    change C lam * Rmap (X 2 - 2 * X 0 * G 0) + C (-b) * F + C (-d) * Rmap ((G 0) ^ 2) = _
    simp only [map_sub, map_mul, map_pow, map_ofNat, MvPolynomial.map_X, map_neg]
    rw [h₁]
    ring
  have hV := scalar_functional_descends_polynomial_linear_combination A (G 1) c φ hSum
  rw [hφ, map_one, one_mul, Fin.sum_univ_three] at hV
  change C μ * (X 2 - 2 * X 0 * G 0) + C (φ (-b)) * G 0 + C (φ (-d)) * (G 0) ^ 2 = G 1 at hV
  have hV' : G 1 = C μ * (X 2 - 2 * X 0 * G 0) - C B * G 0 - C D * (G 0) ^ 2 := by
    rw [← hV]
    simp only [B, D, map_neg]
    ring
  have hVC : C (lam - j μ) * (X 2 - 2 * X 0 * F) + C (j B - b) * F + C (j D - d) * F ^ 2 = 0 := by
    have he := congrArg Rmap hV'
    simp only [map_sub, map_mul, map_pow, map_ofNat, MvPolynomial.map_X, MvPolynomial.map_C] at he
    change Rmap (G 1) = C (j μ) * (X 2 - 2 * X 0 * F) - C (j B) * F - C (j D) * F ^ 2 at he
    simp only [map_sub]
    linear_combination he - h₁
  obtain ⟨hμ, hB, hD⟩ := ternary_parabolic_output_coefficients_unique F Q hQ hAxis _ _ _ hVC
  have hμ' : lam = j μ := sub_eq_zero.mp hμ
  have hB' : j B = b := sub_eq_zero.mp hB
  have hD' : j D = d := sub_eq_zero.mp hD
  have hm : μ ≠ 0 := fun h => hlam (by rw [hμ', h, map_zero])
  have hMap : (algebraMap E Rₑ).comp j = (Rmap).comp (algebraMap K R₃) := by
    apply RingHom.ext
    intro e
    change C (j e) = Rmap (C e)
    rw [MvPolynomial.map_C]
  refine ⟨μ, B, D, p, hm, hp, hp₀, ?_, hV', ?_⟩
  · apply MvPolynomial.map_injective _ (algebraMap K E).injective
    rw [Polynomial.map_aeval_eq_aeval_map hMap, hP]
    simp only [map_add, map_mul, map_pow, MvPolynomial.map_C, MvPolynomial.map_X, hB', hD', ← hμ']
    exact h₀
  · apply MvPolynomial.map_injective _ (algebraMap K E).injective
    rw [map_pow, h₂]

end DimensionFourDependence
