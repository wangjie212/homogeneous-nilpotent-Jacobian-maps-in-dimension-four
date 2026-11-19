import DimensionFourDependence.TernaryQuadraticRelationTransport
import DimensionFourDependence.AffineTangentCoefficientDescent

/-! # The square and linear relation covectors descend to the original field -/

namespace DimensionFourDependence

open MvPolynomial Matrix

universe u
set_option maxHeartbeats 4500000

variable {K E : Type u} [Field K] [Field E] [Algebra K E]
local notation "R₃" => MvPolynomial (Fin 3) K
local notation "Rₑ" => MvPolynomial (Fin 3) E
local notation "j" => (algebraMap K E)
local notation "Rmap" => (MvPolynomial.map (σ := Fin 3) j)

/-- A scalar functional sends an identity among extended original
polynomials to the corresponding identity with original coefficients. -/
theorem scalar_functional_descends_polynomial_linear_combination
    {I : Type*} [Fintype I] {σ : Type*}
    (A : I → MvPolynomial σ K) (p : MvPolynomial σ K) (c : I → E) (φ : E →ₗ[K] K)
    (h : ∑ i, C (c i) * MvPolynomial.map j (A i) = MvPolynomial.map j p) :
    ∑ i, C (φ (c i)) * A i = C (φ 1) * p := by
  have hScalar (a : E) (b : K) : φ (a * j b) = φ a * b := by
    rw [mul_comm, ← Algebra.smul_def, map_smul, smul_eq_mul, mul_comm]
  ext m
  have he := congrArg (fun w : MvPolynomial σ E => φ (w.coeff m)) h
  simp only [coeff_sum, coeff_C_mul, coeff_map, map_sum, hScalar] at he ⊢
  have hFix (b : K) : φ (j b) = φ 1 * b := by simpa only [one_mul] using hScalar 1 b
  exact he.trans (hFix _)

theorem ternary_quadratic_relation_scalar_functional_descends
    (H : Fin 3 → R₃) (l : Fin 3 → E) (Q : Matrix (Fin 3) (Fin 3) E) (φ : E →ₗ[K] K)
    (h : ternaryQuadraticRelation l Q (fun i => Rmap (H i)) = 0) :
    ternaryQuadraticRelation (fun i => φ (l i)) (Q.map φ) H = 0 := by
  have hScalar (a : E) (b : K) : φ (a * j b) = φ a * b := by
    rw [mul_comm, ← Algebra.smul_def, map_smul, smul_eq_mul, mul_comm]
  ext m
  have he := congrArg (fun w : Rₑ => φ (w.coeff m)) h
  simp only [ternaryQuadraticRelation, Matrix.map_apply, mul_assoc, ← map_mul Rmap, AddMonoidAlgebra.coeff_sub,
    Finsupp.sub_apply, coeff_sum, coeff_C_mul, coeff_map, map_sum, map_sub, hScalar,
    AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply, map_zero] at he ⊢
  exact he

theorem ternary_quadratic_relation_scalar_extension
    (H : Fin 3 → R₃) (l : Fin 3 → K) (Q : Matrix (Fin 3) (Fin 3) K) :
    ternaryQuadraticRelation (j ∘ l) (Q.map j) (fun i => Rmap (H i)) = Rmap (ternaryQuadraticRelation l Q H) := by
  simp only [ternaryQuadraticRelation, map_sub, map_sum, map_mul, MvPolynomial.map_C, Function.comp_apply,
    Matrix.map_apply]

variable [CharZero E]

/-- If a normalizing frame exists over an extension, its first and
third covectors are proportional to original covectors with the
compatible scale factors of the parabolic relation. -/
theorem ternary_normalizing_outer_covectors_descend
    (H : Fin 3 → R₃) (T S : Matrix (Fin 3) (Fin 3) E) (hTS : T * S = 1) (hST : S * T = 1)
    (P : Polynomial E) (hP : 0 < P.natDegree)
    (he : linearPolynomialConjugate T S (fun i => Rmap (H i)) = TernaryNormalForm.perturbation3 P) :
    ∃ (t : E) (a b : Fin 3 → K), t ≠ 0 ∧
      (∀ i, S 0 i = t * j (a i)) ∧ ∀ i, S 2 i = t ^ 2 * j (b i) := by
  let G : Fin 3 → Rₑ := fun i => Rmap (H i)
  obtain ⟨k, hk⟩ : ∃ k, S 0 k ≠ 0 := by
    by_contra! h
    have hz := congrFun (congrFun hST 0) 0
    simp [Matrix.mul_apply, h] at hz
  have hOutput := ternary_normalizing_matrix_output_identity G T S hTS P he
  have hSquare : (S.map C *ᵥ G) 2 = (S.map C *ᵥ G) 0 ^ 2 := by
    rw [hOutput]
    change aeval (linearPolynomialMap S)
      ((Polynomial.aeval (X 1 + (X 0 : Rₑ) ^ 2) P) ^ 2) =
      (aeval (linearPolynomialMap S) (Polynomial.aeval (X 1 + (X 0 : Rₑ) ^ 2) P)) ^ 2
    rw [map_pow]
  let W : Matrix (Fin 3) (Fin 3) E := vecMulVec (S 0) (S 0)
  have hW (i i' : Fin 3) : W i i' = S 0 i * S 0 i' := rfl
  have hr : ternaryQuadraticRelation (S 2) W G = 0 := by
    rw [ternaryQuadraticRelation_dot]
    have hL : (C ∘ S 2) ⬝ᵥ G = (S.map C *ᵥ G) 2 := rfl
    have hR : W.map (C : E →+* Rₑ) = vecMulVec (C ∘ S 0) (C ∘ S 0) := by
      ext i i'
      simp only [Matrix.map_apply, hW, vecMulVec_apply, Function.comp_apply, map_mul]
    have hD : (C ∘ S 0) ⬝ᵥ G = (S.map C *ᵥ G) 0 := rfl
    rw [hL, hR, vecMulVec_mulVec, dotProduct_smul, dotProduct_comm G, hD]
    change (S.map C *ᵥ G) 2 - ((S.map C *ᵥ G) 0) * ((S.map C *ᵥ G) 0) = 0
    rw [← pow_two, hSquare, sub_self]
  obtain ⟨φ, hφ⟩ : ∃ φ : E →ₗ[K] K, φ (W k k) ≠ 0 := by
    by_contra! h
    have hz := (Module.forall_dual_apply_eq_zero_iff K (W k k)).mp h
    exact (mul_ne_zero hk hk) hz
  let l : Fin 3 → K := fun i => φ (S 2 i)
  let Q : Matrix (Fin 3) (Fin 3) K := W.map φ
  have hQ : (Q.map j)ᵀ = Q.map j := by
    ext i i'
    change j (φ (W i' i)) = j (φ (W i i'))
    rw [hW, hW, mul_comm]
  have hR₀ := ternary_quadratic_relation_scalar_functional_descends H (S 2) W φ hr
  have hR : ternaryQuadraticRelation (j ∘ l) (Q.map j) G = 0 := by
    rw [ternary_quadratic_relation_scalar_extension _ _ _, hR₀, map_zero]
  obtain ⟨c, hc₁, hc₂⟩ := conjugate_ternary_normal_form_quadratic_relation_unique G T S hTS hST P hP he
    (j ∘ l) (Q.map j) hQ hR
  let d := Q k k
  have hd : d ≠ 0 := hφ
  have hδ : j d = c * S 0 k * S 0 k := hc₂ k k
  have hc : c ≠ 0 := by
    intro h
    rw [h, zero_mul, zero_mul] at hδ
    exact hd ((algebraMap K E).injective (hδ.trans (map_zero j).symm))
  let a : Fin 3 → K := fun i => Q k i / d
  let b : Fin 3 → K := fun i => l i / d
  refine ⟨S 0 k, a, b, hk, ?_, ?_⟩
  · intro i
    change S 0 i = S 0 k * j (Q k i / d)
    have hki : j (Q k i) = c * S 0 k * S 0 i := hc₂ k i
    rw [map_div₀, hki, hδ]
    field_simp [hc, hk]
  · intro i
    change S 2 i = S 0 k ^ 2 * j (l i / d)
    have hi : j (l i) = c * S 2 i := hc₁ i
    rw [map_div₀, hi, hδ]
    field_simp [hc, hk]

end DimensionFourDependence
