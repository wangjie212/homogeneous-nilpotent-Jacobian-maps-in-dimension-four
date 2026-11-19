import DimensionFourDependence.TernaryOriginalCoefficientMaps
import DimensionFourDependence.HomogenizedTernaryNormalForm

/-! # A constant frame over the original field straightens both outer covectors -/

namespace DimensionFourDependence

open MvPolynomial Matrix

universe u
set_option maxHeartbeats 4200000

variable {K E : Type u} [Field K] [Field E] [Algebra K E]
local notation "M₃" => Matrix (Fin 3) (Fin 3) K
local notation "Mₑ" => Matrix (Fin 3) (Fin 3) E
local notation "R₃" => MvPolynomial (Fin 3) K
local notation "j" => (algebraMap K E)
local notation "Rmap" => (MvPolynomial.map (σ := Fin 3) j)

private theorem determinant_middle_row_expansion {F : Type*} [Field F] (M : Matrix (Fin 3) (Fin 3) F) :
    M.det = M 1 0 * (M 0 2 * M 2 1 - M 0 1 * M 2 2) +
      M 1 1 * (M 0 0 * M 2 2 - M 0 2 * M 2 0) +
      M 1 2 * (M 0 1 * M 2 0 - M 0 0 * M 2 1) := by
  rw [Matrix.det_fin_three]
  ring

/-- Two original covectors proportional to the outer rows of an
invertible extension-field matrix extend to an original inverse pair. -/
theorem ternary_outer_covectors_extend_to_original_frame
    (S : Mₑ) (hS : S.det ≠ 0) (t : E) (a b : Fin 3 → K)
    (h₀ : ∀ i, S 0 i = t * j (a i)) (h₂ : ∀ i, S 2 i = t ^ 2 * j (b i)) :
    ∃ A B : M₃, A * B = 1 ∧ B * A = 1 ∧ (∀ i, A 0 i = a i) ∧ ∀ i, A 2 i = b i := by
  let d : Fin 3 → K := ![a 2 * b 1 - a 1 * b 2, a 0 * b 2 - a 2 * b 0, a 1 * b 0 - a 0 * b 1]
  have hdet : S.det = t ^ 3 * ∑ i, S 1 i * j (d i) := by
    rw [determinant_middle_row_expansion S, Fin.sum_univ_three]
    simp only [h₀, h₂]
    change _ = t ^ 3 * (S 1 0 * j (a 2 * b 1 - a 1 * b 2) +
      S 1 1 * j (a 0 * b 2 - a 2 * b 0) + S 1 2 * j (a 1 * b 0 - a 0 * b 1))
    simp only [map_sub, map_mul]
    ring
  obtain ⟨k, hk⟩ : ∃ i, d i ≠ 0 := by
    by_contra! h
    exact hS (by simp [hdet, h])
  let e : Fin 3 → K := Pi.single k 1
  let A : M₃ := of ![a, e, b]
  have hA : A.det = d k := by
    rw [determinant_middle_row_expansion A]
    change e 0 * (a 2 * b 1 - a 1 * b 2) + e 1 * (a 0 * b 2 - a 2 * b 0) +
      e 2 * (a 1 * b 0 - a 0 * b 1) = d k
    fin_cases k <;> simp [e, d]
  have hU : IsUnit A.det := isUnit_iff_ne_zero.mpr (hA.symm ▸ hk)
  exact ⟨A, A⁻¹, Matrix.mul_nonsing_inv A hU, Matrix.nonsing_inv_mul A hU, fun _ => rfl, fun _ => rfl⟩

/-- A normalizing frame over a field extension is put in the outer
coordinate form by one original-field conjugacy. -/
theorem ternary_extension_normalizer_reframes_with_original_outer_coordinates
    (H : Fin 3 → R₃) (T S : Mₑ) (hTS : T * S = 1) (hST : S * T = 1)
    (P : Polynomial E) (he : linearPolynomialConjugate T S (fun i => Rmap (H i)) = TernaryNormalForm.perturbation3 P)
    (t : E) (a b : Fin 3 → K) (h₀ : ∀ i, S 0 i = t * j (a i)) (h₂ : ∀ i, S 2 i = t ^ 2 * j (b i)) :
    ∃ (A B : M₃) (T' S' : Mₑ), A * B = 1 ∧ B * A = 1 ∧ T' * S' = 1 ∧ S' * T' = 1 ∧
      (∀ i, S' 0 i = if i = 0 then t else 0) ∧ (∀ i, S' 2 i = if i = 2 then t ^ 2 else 0) ∧
      linearPolynomialConjugate T' S' (fun i => Rmap (linearPolynomialConjugate B A H i)) =
        TernaryNormalForm.perturbation3 P := by
  have hS : S.det ≠ 0 := by
    have h := congrArg Matrix.det hTS
    rw [Matrix.det_mul, Matrix.det_one] at h
    intro hz
    rw [hz, mul_zero] at h
    exact zero_ne_one h
  obtain ⟨A, B, hAB, hBA, ha, hb⟩ := ternary_outer_covectors_extend_to_original_frame S hS t a b h₀ h₂
  let A' := A.map j
  let B' := B.map j
  have hA' : A' * B' = 1 := by
    change A.map j * B.map j = 1
    rw [← Matrix.map_mul, hAB, Matrix.map_one _ (map_zero j) (map_one j)]
  have hB' : B' * A' = 1 := by
    change B.map j * A.map j = 1
    rw [← Matrix.map_mul, hBA, Matrix.map_one _ (map_zero j) (map_one j)]
  let T' := A' * T
  let S' := S * B'
  have hp : T' * S' = A' * B' := by
    change (A' * T) * (S * B') = A' * B'
    rw [Matrix.mul_assoc A' T, ← Matrix.mul_assoc T S, hTS, Matrix.one_mul]
  have hq : S' * T' = S * T := by simp [T', S', Matrix.mul_assoc, ← Matrix.mul_assoc B' A' T, hB']
  refine ⟨A, B, T', S', hAB, hBA, hp.trans hA', hq.trans hST, ?_, ?_, ?_⟩
  · intro i
    change (S * B') 0 i = _
    simp only [Matrix.mul_apply, h₀, ← ha, mul_assoc, ← Finset.mul_sum]
    have h : ∑ k, j (A 0 k) * B' k i = (1 : Mₑ) 0 i := congrFun (congrFun hA' 0) i
    rw [h, Matrix.one_apply]
    by_cases hi : i = 0 <;> simp [hi, Ne.symm]
  · intro i
    change (S * B') 2 i = _
    simp only [Matrix.mul_apply, h₂, ← hb, mul_assoc, ← Finset.mul_sum]
    have h : ∑ k, j (A 2 k) * B' k i = (1 : Mₑ) 2 i := congrFun (congrFun hA' 2) i
    rw [h, Matrix.one_apply]
    by_cases hi : i = 2 <;> simp [hi, Ne.symm]
  · rw [ternary_linear_conjugate_scalar_extension, linearPolynomialConjugate_compose]
    have h₁ : B' * T' = T := by change B' * (A' * T) = T; rw [← Matrix.mul_assoc, hB', Matrix.one_mul]
    have h₂ : S' * A' = S := by change (S * B') * A' = S; rw [Matrix.mul_assoc, hB', Matrix.mul_one]
    change linearPolynomialConjugate (B' * T') (S' * A') _ = _
    rw [h₁, h₂, he]

end DimensionFourDependence
