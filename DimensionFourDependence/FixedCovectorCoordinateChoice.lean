import DimensionFourDependence.LinearPolynomialConjugacy
import DimensionFourDependence.ActualCompleteFixedConeForms
import DimensionFourDependence.PointAdaptedCoordinates

/-! # A fixed nonzero ternary covector becomes a source coordinate

The covector itself constructs mutually inverse original constant matrices.
Their block extensions fix the vertex coordinate and carry its entire
source linear form to the selected transverse coordinate.
-/

namespace DimensionFourDependence

open MvPolynomial Matrix

set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 100000

variable {K : Type*} [Field K] {n : ℕ}

/-- Every nonzero covector constructs inverse coordinate matrices
sending its full coefficient pairing to a specified coordinate. -/
theorem nonzero_covector_constructs_inverse_coordinate_matrices
    (c : Fin n → K) (hc : c ≠ 0) (j : Fin n) :
    ∃ T S : Matrix (Fin n) (Fin n) K,
      T * S = 1 ∧ S * T = 1 ∧ ∀ k, ∑ i, c i * T i k = if k = j then 1 else 0 := by
  classical
  have he : (Pi.single j 1 : Fin n → K) ≠ 0 := by
    intro hz
    have h := congrFun hz j
    simp only [Pi.single_eq_same, Pi.zero_apply, one_ne_zero] at h
  obtain ⟨g, hg⟩ := exists_linearEquiv_map_nonzero_vector (F := K) c (Pi.single j 1) hc he
  let A := LinearMap.toMatrix' g.toLinearMap
  let B := LinearMap.toMatrix' g.symm.toLinearMap
  have hAB : A * B = 1 := by
    rw [← LinearMap.toMatrix'_comp]
    have heq : g.toLinearMap.comp g.symm.toLinearMap = LinearMap.id := by
      apply LinearMap.ext
      intro x
      exact g.apply_symm_apply x
    rw [heq, LinearMap.toMatrix'_id]
  have hBA : B * A = 1 := by
    rw [← LinearMap.toMatrix'_comp]
    have heq : g.symm.toLinearMap.comp g.toLinearMap = LinearMap.id := by
      apply LinearMap.ext
      intro x
      exact g.symm_apply_apply x
    rw [heq, LinearMap.toMatrix'_id]
  have hAc : A *ᵥ c = Pi.single j 1 := by
    change (Matrix.toLin' (LinearMap.toMatrix' g.toLinearMap)) c = _
    rw [Matrix.toLin'_toMatrix']
    exact hg
  refine ⟨A.transpose, B.transpose, ?_, ?_, ?_⟩
  · rw [← Matrix.transpose_mul, hBA, Matrix.transpose_one]
  · rw [← Matrix.transpose_mul, hAB, Matrix.transpose_one]
  · intro k
    simpa only [Matrix.transpose_apply, Matrix.mulVec, dotProduct, Pi.single_apply,
      mul_comm] using congrFun hAc k

/-- Extend a transverse coordinate matrix by the identity on the
original vertex coordinate. -/
noncomputable def vertexPreservingMatrix (T : Matrix (Fin n) (Fin n) K) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) K :=
  fun i j => Fin.lastCases (Fin.lastCases 1 (fun _ => 0) j)
    (fun i => Fin.lastCases 0 (fun j => T i j) j) i

/-- The transverse block of the constructed extension is unchanged. -/
theorem vertexPreservingMatrix_castSucc
    (T : Matrix (Fin n) (Fin n) K) (i j : Fin n) :
    vertexPreservingMatrix T i.castSucc j.castSucc = T i j := by
  simp [vertexPreservingMatrix]

/-- The last row is exactly the fixed vertex-coordinate row. -/
theorem vertexPreservingMatrix_last_row
    (T : Matrix (Fin n) (Fin n) K) (j : Fin (n + 1)) :
    vertexPreservingMatrix T (Fin.last n) j = if j = Fin.last n then 1 else 0 := by
  refine Fin.lastCases ?_ (fun j => ?_) j <;> simp [vertexPreservingMatrix]

/-- Extending by the fixed vertex coordinate respects matrix products. -/
theorem vertexPreservingMatrix_mul
    (T S : Matrix (Fin n) (Fin n) K) :
    vertexPreservingMatrix T * vertexPreservingMatrix S = vertexPreservingMatrix (T * S) := by
  ext i j
  refine Fin.lastCases ?_ (fun i => ?_) i
  · refine Fin.lastCases ?_ (fun j => ?_) j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_castSucc, vertexPreservingMatrix]
  · refine Fin.lastCases ?_ (fun j => ?_) j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_castSucc, vertexPreservingMatrix]

/-- The extended transverse identity is the full identity. -/
theorem vertexPreservingMatrix_one :
    vertexPreservingMatrix (1 : Matrix (Fin n) (Fin n) K) = 1 := by
  ext i j
  refine Fin.lastCases ?_ (fun i => ?_) i
  · refine Fin.lastCases ?_ (fun j => ?_) j <;> simp [vertexPreservingMatrix, Matrix.one_apply, eq_comm]
  · refine Fin.lastCases ?_ (fun j => ?_) j <;> simp [vertexPreservingMatrix, Matrix.one_apply, eq_comm]

/-- Pullback of a complete original linear form is its coefficient
row multiplied by the coordinate matrix. -/
theorem linearPolynomialPullback_linear_form
    (T : Matrix (Fin n) (Fin n) K) (c : Fin n → K) :
    linearPolynomialPullback T (linearFormPolynomial c) =
      linearFormPolynomial (fun j => ∑ i, c i * T i j) := by
  simp only [linearPolynomialPullback, linearFormPolynomial, map_sum, map_mul,
    aeval_C, aeval_X, linearPolynomialMap, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [algebraMap_eq, mul_assoc]

/-- Every transverse coordinate substitution commutes with its actual
inclusion in the original source polynomial ring. -/
theorem vertexPreservingMatrix_transverse_pullback
    (T : Matrix (Fin n) (Fin n) K) (p : MvPolynomial (Fin n) K) :
    linearPolynomialPullback (vertexPreservingMatrix T) (rename Fin.castSucc p) =
      rename Fin.castSucc (linearPolynomialPullback T p) := by
  have heq : (aeval (linearPolynomialMap (vertexPreservingMatrix T))).comp
      (rename Fin.castSucc) =
        (rename Fin.castSucc).comp (aeval (linearPolynomialMap T)) := by
    apply MvPolynomial.algHom_ext
    intro i
    simp only [AlgHom.comp_apply, rename_X, aeval_X, linearPolynomialMap,
      map_sum, map_mul, rename_C]
    rw [Fin.sum_univ_castSucc]
    simp [vertexPreservingMatrix]
  exact AlgHom.congr_fun heq p

/-- The extended coordinate change fixes the full vertex polynomial. -/
theorem vertexPreservingMatrix_vertex_pullback
    (T : Matrix (Fin n) (Fin n) K) :
    linearPolynomialPullback (vertexPreservingMatrix T) (X (Fin.last n)) = X (Fin.last n) := by
  simp [linearPolynomialPullback, linearPolynomialMap, vertexPreservingMatrix,
    Fin.sum_univ_castSucc]

/-- The actual fixed ternary source linear form constructs a full
inverse source-coordinate pair, fixing the original vertex and making
the specified transverse variable equal to that linear form. -/
theorem fixed_covector_constructs_vertex_preserving_source_coordinates
    (c : Fin n → K) (hc : c ≠ 0) (j : Fin n) :
    ∃ T S : Matrix (Fin n) (Fin n) K,
      vertexPreservingMatrix T * vertexPreservingMatrix S = 1 ∧
      vertexPreservingMatrix S * vertexPreservingMatrix T = 1 ∧
      linearPolynomialPullback (vertexPreservingMatrix T)
        (rename Fin.castSucc (linearFormPolynomial c)) = X j.castSucc ∧
      linearPolynomialPullback (vertexPreservingMatrix T) (X (Fin.last n)) = X (Fin.last n) := by
  obtain ⟨T, S, hTS, hST, hrow⟩ := nonzero_covector_constructs_inverse_coordinate_matrices c hc j
  refine ⟨T, S, ?_, ?_, ?_, vertexPreservingMatrix_vertex_pullback T⟩
  · rw [vertexPreservingMatrix_mul, hTS, vertexPreservingMatrix_one]
  · rw [vertexPreservingMatrix_mul, hST, vertexPreservingMatrix_one]
  · rw [vertexPreservingMatrix_transverse_pullback, linearPolynomialPullback_linear_form]
    have hr : (fun k => ∑ i, c i * T i k) = Pi.single j 1 := by
      funext k
      simpa only [Pi.single_apply] using hrow k
    rw [hr]
    simp [linearFormPolynomial, Pi.single_apply]

end DimensionFourDependence
