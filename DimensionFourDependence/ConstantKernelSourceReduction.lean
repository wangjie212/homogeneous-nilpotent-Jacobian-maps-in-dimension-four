import DimensionFourDependence.CommonVertexCoordinateChoice
import DimensionFourDependence.PolynomialKernelConjugacy
import DimensionFourDependence.BinaryBlockNilpotence
import DimensionFourDependence.ReducedPencilVertexDifferential

/-! # A constant right-kernel direction removes an actual source variable -/

namespace DimensionFourDependence

open MvPolynomial Matrix

set_option maxHeartbeats 3000000

variable {K : Type*} [Field K] {n : ℕ}

/-- A nonzero original vector constructs both inverse matrices and its
specified coordinate-vector image under the inverse matrix. -/
theorem nonzero_vector_constructs_inverse_coordinate_image
    (c : Fin n → K) (hc : c ≠ 0) (j : Fin n) :
    ∃ T S : Matrix (Fin n) (Fin n) K,
      T * S = 1 ∧ S * T = 1 ∧ S *ᵥ c = Pi.single j 1 := by
  classical
  obtain ⟨T, S, hTS, hST, hcol⟩ :=
    nonzero_vector_constructs_inverse_coordinate_matrices c hc j
  have hTc : T *ᵥ (Pi.single j 1) = c := by
    funext i
    simpa only [Matrix.mulVec, dotProduct_single, mul_one] using hcol i
  refine ⟨T, S, hTS, hST, ?_⟩
  rw [← hTc, Matrix.mulVec_mulVec, hST, Matrix.one_mulVec]

/-- The constant kernel direction constructs coordinates in which
every original transformed component has zero selected partial. -/
theorem constant_right_kernel_constructs_coordinate_partial_zero
    (H : Fin n → MvPolynomial (Fin n) K)
    (c : Fin n → K) (hc : c ≠ 0)
    (hker : jac H *ᵥ (fun i => C (c i)) = 0) (j : Fin n) :
    ∃ T S : Matrix (Fin n) (Fin n) K,
      T * S = 1 ∧ S * T = 1 ∧
      ∀ i, pderiv j (linearPolynomialConjugate T S H i) = 0 := by
  classical
  obtain ⟨T, S, hTS, hST, hSc⟩ :=
    nonzero_vector_constructs_inverse_coordinate_image c hc j
  have hconst : linearPolynomialConjugate T S (fun i => C (c i)) =
      fun i => C ((Pi.single j 1 : Fin n → K) i) := by
    funext i
    change (∑ k, C (S i k) * linearPolynomialPullback T (C (c k))) = _
    simp only [linearPolynomialPullback, aeval_C, algebraMap_eq,
      ← map_mul, ← map_sum]
    exact congrArg C (congrFun hSc i)
  have hk := linearPolynomialConjugate_preserves_polynomial_right_kernel
    T S hTS H (fun i => C (c i)) hker
  rw [hconst] at hk
  refine ⟨T, S, hTS, hST, ?_⟩
  intro i
  have hi := congrFun hk i
  simpa [Matrix.mulVec, dotProduct, jac, Pi.single_apply] using hi

variable [CharZero K]

/-- A zero last partial produces a polynomial over the smaller source
ring. This constructs the representative rather than only its degree. -/
theorem zero_last_partial_constructs_smaller_source_polynomial
    (P : MvPolynomial (Fin (n + 1)) K)
    (hP : pderiv (Fin.last n) P = 0) :
    ∃ Q : MvPolynomial (Fin n) K, rename Fin.castSucc Q = P := by
  classical
  apply exists_rename_eq_of_vars_subset_range P Fin.castSucc (Fin.castSucc_injective n)
  intro i hi
  have hne : i ≠ Fin.last n := by
    intro heq
    subst i
    exact (mem_vars_iff_degreeOf_ne_zero.mp hi)
      (degreeOf_eq_zero_of_pderiv_eq_zero P (Fin.last n) hP)
  exact Fin.eq_castSucc_of_ne_last hne

/-- An ambient matrix with zero last column has a nilpotent leading
block whenever the actual ambient matrix is nilpotent. -/
theorem leading_block_isNilpotent_of_last_column_zero
    {R : Type*} [CommRing R]
    (M : Matrix (Fin (n + 1)) (Fin (n + 1)) R)
    (hM : IsNilpotent M) (hzero : ∀ i, M i (Fin.last n) = 0) :
    IsNilpotent (M.submatrix Fin.castSucc Fin.castSucc) := by
  classical
  let P : Matrix (Fin n) (Fin (n + 1)) R := fun i j => if i.castSucc = j then 1 else 0
  have hPI : P * P.transpose = 1 := by
    funext i j
    change (∑ k, P i k * P j k) = if i = j then 1 else 0
    simp [P, Fin.castSucc_inj, eq_comm]
  have hcompat : P * M = M.submatrix Fin.castSucc Fin.castSucc * P := by
    funext i j
    refine Fin.lastCases ?_ (fun j => ?_) j
    · change (∑ k, P i k * M k (Fin.last n)) =
        ∑ k, M i.castSucc k.castSucc * P k (Fin.last n)
      simp [P, hzero]
    · change (∑ k, P i k * M k j.castSucc) =
        ∑ k, M i.castSucc k.castSucc * P k j.castSucc
      simp [P, Fin.castSucc_inj]
  exact matrix_isNilpotent_of_split_quotient M _ P P.transpose hPI hcompat hM

/-- A homogeneous map and an original nonzero constant right-kernel
construct inverse source-target coordinates and all smaller-source
forms. The first n forms have an actually nilpotent Jacobian over their
own polynomial ring. No coordinate or block hypotheses are supplied. -/
theorem homogeneous_nilpotent_constant_kernel_constructs_smaller_source_map
    (H : Fin (n + 1) → MvPolynomial (Fin (n + 1)) K) {d : ℕ}
    (hH : IsHomogMap H d) (hN : IsNilpotent (jac H))
    (c : Fin (n + 1) → K) (hc : c ≠ 0)
    (hker : jac H *ᵥ (fun i => C (c i)) = 0) :
    ∃ (T S : Matrix (Fin (n + 1)) (Fin (n + 1)) K)
      (G : Fin (n + 1) → MvPolynomial (Fin n) K),
      T * S = 1 ∧ S * T = 1 ∧
      (∀ i, rename Fin.castSucc (G i) = linearPolynomialConjugate T S H i) ∧
      (∀ i, (G i).IsHomogeneous d) ∧
      IsNilpotent (jac (fun i : Fin n => G i.castSucc)) := by
  classical
  obtain ⟨T, S, hTS, hST, hpartial⟩ :=
    constant_right_kernel_constructs_coordinate_partial_zero H c hc hker (Fin.last n)
  choose G hG using fun i => zero_last_partial_constructs_smaller_source_polynomial
    (linearPolynomialConjugate T S H i) (hpartial i)
  have hhom := linearPolynomialConjugate_homogeneous T S H hH
  have hnil := linearPolynomialConjugate_nilpotent T S hTS hST H hN
  have hblock := leading_block_isNilpotent_of_last_column_zero
    (jac (linearPolynomialConjugate T S H)) hnil hpartial
  have hmat : (jac (fun i : Fin n => G i.castSucc)).map
      (rename Fin.castSucc : MvPolynomial (Fin n) K →ₐ[K] MvPolynomial (Fin (n + 1)) K) =
      (jac (linearPolynomialConjugate T S H)).submatrix Fin.castSucc Fin.castSucc := by
    funext i j
    change rename Fin.castSucc (pderiv j (G i.castSucc)) =
      pderiv j.castSucc (linearPolynomialConjugate T S H i.castSucc)
    rw [← hG]
    exact (pderiv_rename (Fin.castSucc_injective n) j (G i.castSucc)).symm
  have hsmall : IsNilpotent (jac (fun i : Fin n => G i.castSucc)) := by
    obtain ⟨k, hk⟩ := hblock
    refine ⟨k, ?_⟩
    apply Matrix.map_injective (rename_injective Fin.castSucc (Fin.castSucc_injective n))
    change ((jac (fun i : Fin n => G i.castSucc)) ^ k).map (rename Fin.castSucc).toRingHom = _
    rw [Matrix.map_pow]
    change ((jac (fun i : Fin n => G i.castSucc)).map (rename Fin.castSucc)) ^ k = _
    rw [hmat, hk]
    rfl
  refine ⟨T, S, G, hTS, hST, hG, ?_, hsmall⟩
  intro i
  apply (IsHomogeneous.rename_isHomogeneous_iff (Fin.castSucc_injective n)).mp
  rw [hG]
  exact hhom i

end DimensionFourDependence
