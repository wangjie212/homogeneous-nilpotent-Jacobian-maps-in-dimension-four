import DimensionFourDependence.TernaryNormalFormRelation
import DimensionFourDependence.LinearConjugacyComposition

/-! # Transport of the normalized quadratic relation to the original coordinates -/

namespace DimensionFourDependence

open MvPolynomial Matrix

universe u
set_option maxHeartbeats 3700000

variable {K : Type u} [Field K]
local notation "R₃" => MvPolynomial (Fin 3) K
local notation "M₃" => Matrix (Fin 3) (Fin 3) K

/-- The relation is a linear form minus a symmetric matrix pairing,
evaluated literally on the original polynomial outputs. -/
theorem ternaryQuadraticRelation_dot (l : Fin 3 → K) (Q : M₃) (H : Fin 3 → R₃) :
    ternaryQuadraticRelation l Q H = (C ∘ l) ⬝ᵥ H - H ⬝ᵥ (Q.map C *ᵥ H) := by
  unfold ternaryQuadraticRelation
  congr 1
  simp only [dotProduct, Matrix.mulVec, Matrix.map_apply, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- A constant target frame transports the linear relation covector and
the quadratic pairing by the original matrix and its transpose. -/
theorem ternaryQuadraticRelation_target_matrix (l : Fin 3 → K) (Q T : M₃) (H : Fin 3 → R₃) :
    ternaryQuadraticRelation l Q (T.map C *ᵥ H) = ternaryQuadraticRelation (l ᵥ* T) (Tᵀ * Q * T) H := by
  have hL : (C : K →+* R₃) ∘ (l ᵥ* T) = (C ∘ l) ᵥ* T.map C := by
    funext i
    exact RingHom.map_vecMul C T l i
  let B := T.map (C : K →+* R₃)
  let A := Q.map (C : K →+* R₃)
  have hQ : (B *ᵥ H) ⬝ᵥ (A *ᵥ (B *ᵥ H)) = H ⬝ᵥ ((Bᵀ * A * B) *ᵥ H) := by
    calc
      _ = (H ᵥ* Bᵀ) ⬝ᵥ (A *ᵥ (B *ᵥ H)) := by rw [vecMul_transpose]
      _ = H ⬝ᵥ (Bᵀ *ᵥ (A *ᵥ (B *ᵥ H))) := (dotProduct_mulVec H Bᵀ _).symm
      _ = _ := by rw [mulVec_mulVec H A B, mulVec_mulVec, Matrix.mul_assoc]
  rw [ternaryQuadraticRelation_dot, ternaryQuadraticRelation_dot, hL,
    Matrix.map_mul, Matrix.map_mul, dotProduct_mulVec (C ∘ l)]
  change _ - ((B *ᵥ H) ⬝ᵥ (A *ᵥ (B *ᵥ H))) = _ - H ⬝ᵥ ((Bᵀ * A * B) *ᵥ H)
  rw [hQ]

theorem ternaryQuadraticRelation_source_map (l : Fin 3 → K) (Q : M₃) (H : Fin 3 → R₃)
    (e : R₃ →ₐ[K] R₃) : ternaryQuadraticRelation l Q (fun i => e (H i)) = e (ternaryQuadraticRelation l Q H) := by
  simp only [ternaryQuadraticRelation, map_sub, map_sum, map_mul]
  change _ = (∑ i, e (C (l i)) * e (H i)) - ∑ i, ∑ j, e (C (Q i j)) * e (H i) * e (H j)
  simp only [show ∀ a : K, e (C a) = C a from e.commutes]

theorem ternaryLinearConjugate_one (H : Fin 3 → R₃) : linearPolynomialConjugate 1 1 H = H := by
  have h : linearPolynomialMap (1 : M₃) = (X : Fin 3 → R₃) := by
    funext i
    simp [linearPolynomialMap, Matrix.one_apply]
  funext i
  simp [linearPolynomialConjugate, linearPolynomialPullback, h, Matrix.one_apply]

/-- Conjugacy transports the actual identity of the normalized map
back to an exact identity between original output covectors. -/
theorem ternary_normalizing_matrix_output_identity
    (H : Fin 3 → R₃) (T S : M₃) (hTS : T * S = 1) (P : Polynomial K)
    (he : linearPolynomialConjugate T S H = TernaryNormalForm.perturbation3 P) :
    S.map C *ᵥ H = fun i => linearPolynomialPullback S (TernaryNormalForm.perturbation3 P i) := by
  funext i
  rw [← he]
  change (∑ j, C (S i j) * H j) = aeval (linearPolynomialMap S) (∑ j, C (S i j) * linearPolynomialPullback T (H j))
  simp only [map_sum, map_mul, aeval_C, algebraMap_eq]
  apply Finset.sum_congr rfl
  intro j _
  exact congrArg (fun p : R₃ => C (S i j) * p) (matrix_linear_polynomial_substitution_inverse T S hTS (H j)).symm

variable [CharZero K]

/-- Every symmetric quadratic relation of a conjugate of the canonical
form is a scalar multiple of the actual first and third output covectors. -/
theorem conjugate_ternary_normal_form_quadratic_relation_unique
    (H : Fin 3 → R₃) (T S : M₃) (hTS : T * S = 1) (hST : S * T = 1)
    (P : Polynomial K) (hP : 0 < P.natDegree)
    (he : linearPolynomialConjugate T S H = TernaryNormalForm.perturbation3 P)
    (l : Fin 3 → K) (Q : M₃) (hQ : Qᵀ = Q) (hr : ternaryQuadraticRelation l Q H = 0) :
    ∃ c : K, (∀ i, l i = c * S 2 i) ∧ ∀ i j, Q i j = c * S 0 i * S 0 j := by
  let N := TernaryNormalForm.perturbation3 P
  let e := matrixPolynomialCoordinateEquiv S T hST hTS
  have hH : H = T.map C *ᵥ (fun i => e (N i)) := by
    have h := linearPolynomialConjugate_compose T S S T H
    rw [he, hTS, ternaryLinearConjugate_one] at h
    exact h.symm
  let l' := l ᵥ* T
  let Q' := Tᵀ * Q * T
  have hr' : ternaryQuadraticRelation l' Q' N = 0 := by
    rw [hH, ternaryQuadraticRelation_target_matrix] at hr
    change ternaryQuadraticRelation l' Q' (fun i => e.toAlgHom (N i)) = 0 at hr
    rw [ternaryQuadraticRelation_source_map l' Q' N e.toAlgHom] at hr
    exact e.injective (hr.trans (map_zero e).symm)
  have hQ' : Q'ᵀ = Q' := by
    dsimp only [Q']
    rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, hQ, Matrix.mul_assoc]
  obtain ⟨hl', hq'⟩ := ternary_normal_form_symmetric_quadratic_relation_unique P hP l' Q' hQ' hr'
  have hl : l = l' ᵥ* S := by
    change l = (l ᵥ* T) ᵥ* S
    rw [vecMul_vecMul, hTS, vecMul_one]
  have hq : Q = Sᵀ * Q' * S := by
    change Q = Sᵀ * (Tᵀ * Q * T) * S
    calc
      _ = (T * S)ᵀ * Q * (T * S) := by rw [hTS, Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one]
      _ = _ := by simp only [Matrix.transpose_mul, Matrix.mul_assoc]
  refine ⟨l' 2, ?_, ?_⟩
  · intro i
    have h := congrFun hl i
    change l i = ∑ j, l' j * S j i at h
    have h₀ : l' 0 = 0 := hl' 0
    have h₁ : l' 1 = 0 := hl' 1
    simpa [h₀, h₁, Fin.sum_univ_three] using h
  · intro i j
    have h := congrFun (congrFun hq i) j
    simp only [Matrix.mul_apply, Matrix.transpose_apply, hq', Finset.sum_mul] at h
    simp only [Fin.sum_univ_three] at h
    norm_num at h
    linear_combination h

end DimensionFourDependence
