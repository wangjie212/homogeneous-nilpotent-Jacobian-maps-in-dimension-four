import DimensionFourDependence.TernaryPlanarConstantRelation
import DimensionFourDependence.FixedCoordinateChartLinearConjugacy
import DimensionFourDependence.FixedCoordinateReduction

/-! # Homogeneous ternary maps with one fixed output have a constant triangular frame -/

namespace DimensionFourDependence

open MvPolynomial Matrix

set_option maxHeartbeats 1550000

variable {K : Type*} [Field K] [CharZero K]
local notation "R₃" => MvPolynomial (Fin 3) K
local notation "z" => (X 2 : R₃)

theorem ternary_planar_relation_before_normalization
    (A : Fin 2 → R₃) (d : ℕ) (c : Fin 2 → K)
    (hc : ∑ i, c i • ternaryPlanarNormalized (A i) d = 0) :
    ∃ γ : K, ∑ i, C (c i) * A i = C γ * z ^ d := by
  refine ⟨c 0 * ternaryPlanarScalar (A 0) + c 1 * ternaryPlanarScalar (A 1), ?_⟩
  simp only [Fin.sum_univ_two, smul_eq_C_mul, ternaryPlanarNormalized] at hc
  simp only [Fin.sum_univ_two, map_mul, map_add]
  linear_combination hc

theorem homogeneous_ternary_fixed_last_constructs_triangular_form
    (H : Fin 3 → R₃) {d : ℕ} (hH : IsHomogMap H d) (hN : IsNilpotent (jac H))
    (hz : H (Fin.last 2) = 0) :
    ∃ (U V : Matrix (Fin 3) (Fin 3) K) (B : R₃) (γ : K),
      U * V = 1 ∧ V * U = 1 ∧
      linearPolynomialConjugate U V H = ![B, C γ * z ^ d, 0] ∧ pderiv 0 B = 0 := by
  let A : Fin 2 → R₃ := fun i => H i.castSucc
  let J : Matrix (Fin 3) (Fin 3) R₃ := jac H
  have hrow (j : Fin 3) : J (Fin.last 2) j = 0 := by
    simp only [J, jac, Matrix.of_apply, hz, map_zero]
  have hplan : IsNilpotent (ternaryPlanarJacobian A) :=
    leading_block_isNilpotent_of_last_row_zero J hN hrow
  obtain ⟨c, hc0, hc⟩ := homogeneous_ternary_planar_normalized_componentsDependent A
    (fun i => hH i.castSucc) hplan
  obtain ⟨γ, hγ⟩ := ternary_planar_relation_before_normalization A d c hc
  obtain ⟨T, S, hTS, hST, hS⟩ := nonzero_covector_constructs_inverse_coordinate_row c hc0 1
  let U : Matrix (Fin 3) (Fin 3) K := vertexPreservingMatrix T
  let V : Matrix (Fin 3) (Fin 3) K := vertexPreservingMatrix S
  let G := linearPolynomialConjugate U V H
  have hUV : U * V = 1 := by
    change vertexPreservingMatrix T * vertexPreservingMatrix S = 1
    rw [vertexPreservingMatrix_mul, hTS, vertexPreservingMatrix_one]
  have hVU : V * U = 1 := by
    change vertexPreservingMatrix S * vertexPreservingMatrix T = 1
    rw [vertexPreservingMatrix_mul, hST, vertexPreservingMatrix_one]
  let P : R₃ →ₐ[K] R₃ := aeval (linearPolynomialMap U)
  have hP (a : K) : P (C a) = C a := P.commutes _
  have hPz : P z = z := vertexPreservingMatrix_vertex_pullback T
  have hG₁ : G 1 = C γ * z ^ d := by
    change ∑ j : Fin 3, C (vertexPreservingMatrix S (1 : Fin 2).castSucc j) * P (H j) = _
    rw [Fin.sum_univ_castSucc]
    simp only [vertexPreservingMatrix_castSucc, hS, hz, map_zero, mul_zero, add_zero]
    have he := congrArg P hγ
    simpa only [map_sum, map_mul, map_pow, hP, hPz, A] using he
  have hG₂ : G 2 = 0 := vertexPreserving_conjugate_last_zero T S H hz
  have hn : IsNilpotent (jac G) := linearPolynomialConjugate_nilpotent U V hUV hVU H hN
  have ht := (Matrix.isNilpotent_trace_of_isNilpotent hn).eq_zero
  change (∑ i : Fin 3, pderiv i (G i)) = 0 at ht
  rw [Fin.sum_univ_three] at ht
  have hy : pderiv (1 : Fin 3) (C γ * z ^ d) = 0 := by
    simp [pderiv_mul, pderiv_pow]
  rw [hG₁, hG₂, hy, map_zero, add_zero, add_zero] at ht
  refine ⟨U, V, G 0, γ, hUV, hVU, ?_, ht⟩
  change G = _
  funext i
  fin_cases i
  · rfl
  · exact hG₁
  · exact hG₂

end DimensionFourDependence
