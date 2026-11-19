import DimensionFourDependence.HomogeneousDependenceTheorem
import DimensionFourDependence.CommonVertexCoordinateChoice
import DimensionFourDependence.ConstantKernelSourceReduction

/-! # Section 6.2: the proved relation constructs an actual fixed coordinate -/

namespace DimensionFourDependence

open Matrix MvPolynomial

set_option maxHeartbeats 2500000

variable {K : Type*} [Field K] {n : ℕ}

/-- A nonzero constant covector is an actual specified row of an
invertible coordinate matrix over the original field. -/
theorem nonzero_covector_constructs_inverse_coordinate_row
    (c : Fin n → K) (hc : c ≠ 0) (j : Fin n) :
    ∃ T S : Matrix (Fin n) (Fin n) K,
      T * S = 1 ∧ S * T = 1 ∧ ∀ i, S j i = c i := by
  obtain ⟨A, B, hAB, hBA, hcol⟩ :=
    nonzero_vector_constructs_inverse_coordinate_matrices c hc j
  refine ⟨Bᵀ, Aᵀ, ?_, ?_, hcol⟩
  · rw [← Matrix.transpose_mul, hAB, Matrix.transpose_one]
  · rw [← Matrix.transpose_mul, hBA, Matrix.transpose_one]

/-- A genuine constant component relation constructs the full source
and target conjugacy with the selected perturbation component zero. -/
theorem constant_relation_constructs_zero_component_conjugacy
    (H : Fin n → MvPolynomial (Fin n) K) (hdep : ComponentsDependent H)
    (j : Fin n) :
    ∃ T S : Matrix (Fin n) (Fin n) K,
      T * S = 1 ∧ S * T = 1 ∧ linearPolynomialConjugate T S H j = 0 := by
  obtain ⟨c, hc, hrel⟩ := hdep
  obtain ⟨T, S, hTS, hST, hrow⟩ :=
    nonzero_covector_constructs_inverse_coordinate_row c hc j
  refine ⟨T, S, hTS, hST, ?_⟩
  have he := congrArg (linearPolynomialPullback T) hrel
  simpa only [linearPolynomialConjugate, hrow, linearPolynomialPullback,
    map_sum, map_smul, map_zero, MvPolynomial.smul_eq_C_mul,
    map_mul, aeval_C, MvPolynomial.algebraMap_eq] using he

/-- A zero last row makes the leading block an invariant subspace;
it therefore inherits nilpotence over the actual coefficient ring. -/
theorem leading_block_isNilpotent_of_last_row_zero
    {R : Type*} [CommRing R]
    (M : Matrix (Fin (n + 1)) (Fin (n + 1)) R)
    (hM : IsNilpotent M) (hzero : ∀ j, M (Fin.last n) j = 0) :
    IsNilpotent (M.submatrix Fin.castSucc Fin.castSucc) := by
  have ht := leading_block_isNilpotent_of_last_column_zero Mᵀ
    (Matrix.isNilpotent_transpose_iff.mpr hM) hzero
  exact Matrix.isNilpotent_transpose_iff.mp ht

/-- The leading Jacobian is nilpotent as a matrix of original
polynomials whenever the final perturbation component vanishes. -/
theorem leading_jacobian_isNilpotent_of_last_component_zero
    (H : Fin (n + 1) → MvPolynomial (Fin (n + 1)) K)
    (hN : IsNilpotent (jac H)) (hz : H (Fin.last n) = 0) :
    IsNilpotent ((jac H).submatrix Fin.castSucc Fin.castSucc) := by
  apply leading_block_isNilpotent_of_last_row_zero (jac H) hN
  intro j
  simp only [jac, Matrix.of_apply, hz, map_zero]

variable [CharZero K]

/-- Theorem 1.1 supplies all constant coordinates required at the
start of Section 6.2, with no assumed relation or frame. The leading
three-variable Jacobian remains nilpotent over `K[x,y,z,t]`. -/
theorem original_homogeneous_nilpotent_map_constructs_fixed_coordinate_reduction
    (H : Fin 4 → MvPolynomial (Fin 4) K) {d : ℕ}
    (hd : 0 < d) (hH : IsHomogMap H d) (hN : IsNilpotent (jac H)) :
    ∃ (T S : Matrix (Fin 4) (Fin 4) K)
      (B : Fin 3 → MvPolynomial (Fin 4) K),
      T * S = 1 ∧ S * T = 1 ∧
      linearPolynomialConjugate T S H = Fin.lastCases 0 B ∧
      (∀ i, (B i).IsHomogeneous d) ∧
      IsNilpotent ((jac (Fin.lastCases 0 B)).submatrix Fin.castSucc Fin.castSucc) := by
  obtain ⟨T, S, hTS, hST, hz⟩ :=
    constant_relation_constructs_zero_component_conjugacy H
      (theorem_1_1 d hd H hH hN) (Fin.last 3)
  let G := linearPolynomialConjugate T S H
  let B : Fin 3 → MvPolynomial (Fin 4) K := fun i => G i.castSucc
  have hG : G = Fin.lastCases 0 B := by
    funext i
    exact Fin.lastCases (by simpa only [Fin.lastCases_last] using hz)
      (fun i => by simp only [Fin.lastCases_castSucc]; rfl) i
  refine ⟨T, S, B, hTS, hST, hG, ?_, ?_⟩
  · exact fun i => linearPolynomialConjugate_homogeneous T S H hH i.castSucc
  · rw [← hG]
    exact leading_jacobian_isNilpotent_of_last_component_zero G
      (linearPolynomialConjugate_nilpotent T S hTS hST H hN) hz

end DimensionFourDependence
