import DimensionFourDependence.ImageRelationConjugacy
import DimensionFourDependence.PointAdaptedCoordinates

/-! # An arbitrary nonzero constant vertex supplies actual source-target coordinates -/

namespace DimensionFourDependence

open MvPolynomial Matrix

set_option maxHeartbeats 1500000
set_option synthInstance.maxHeartbeats 100000

variable {K : Type*} [Field K] {n : ℕ}

/-- A nonzero vector can be a specified column of inverse constant
coordinate matrices. The full column, not just its projective direction,
is retained. -/
theorem nonzero_vector_constructs_inverse_coordinate_matrices
    (v : Fin n → K) (hv : v ≠ 0) (j : Fin n) :
    ∃ T S : Matrix (Fin n) (Fin n) K,
      T * S = 1 ∧ S * T = 1 ∧ ∀ i, T i j = v i := by
  classical
  have he : (Pi.single j 1 : Fin n → K) ≠ 0 := by
    intro hzero
    have h := congrFun hzero j
    simp only [Pi.single_eq_same, Pi.zero_apply, one_ne_zero] at h
  obtain ⟨g, hg⟩ := exists_linearEquiv_map_nonzero_vector (F := K) (Pi.single j 1) v he hv
  let T := LinearMap.toMatrix' g.toLinearMap
  let S := LinearMap.toMatrix' g.symm.toLinearMap
  have hTS : T * S = 1 := by
    rw [← LinearMap.toMatrix'_comp]
    have hcomp : g.toLinearMap.comp g.symm.toLinearMap = LinearMap.id := by
      apply LinearMap.ext
      intro x
      exact g.apply_symm_apply x
    rw [hcomp, LinearMap.toMatrix'_id]
  have hST : S * T = 1 := by
    rw [← LinearMap.toMatrix'_comp]
    have hcomp : g.symm.toLinearMap.comp g.toLinearMap = LinearMap.id := by
      apply LinearMap.ext
      intro x
      exact g.symm_apply_apply x
    rw [hcomp, LinearMap.toMatrix'_id]
  have hcol : T *ᵥ Pi.single j 1 = v := by
    change (Matrix.toLin' (LinearMap.toMatrix' g.toLinearMap)) (Pi.single j 1) = v
    rw [Matrix.toLin'_toMatrix']
    exact hg
  refine ⟨T, S, hTS, hST, ?_⟩
  intro i
  simpa only [Matrix.mulVec, dotProduct_single, mul_one] using congrFun hcol i

/-- Every original nonzero common normal annihilator supplies a
conjugated actual image equation whose fourth normal coordinate vanishes. -/
theorem nonzero_common_vertex_constructs_conjugated_image_witness
    (H : Fin 4 → MvPolynomial (Fin 4) K) (I : ImageRelationWitness H)
    (v : Fin 4 → K) (hv : v ≠ 0)
    (hnormal : rationalImageNormal H I.equation ⬝ᵥ
      (fun i => algebraMap K (FractionRing (MvPolynomial (Fin 4) K)) (v i)) = 0) :
    ∃ (T S : Matrix (Fin 4) (Fin 4) K) (hTS : T * S = 1) (hST : S * T = 1),
      (∀ i, T i (Fin.last 3) = v i) ∧
      rationalImageNormal (linearPolynomialConjugate T S H)
        (I.linearConjugate H T S hTS hST).equation (Fin.last 3) = 0 := by
  obtain ⟨T, S, hTS, hST, hcol⟩ := nonzero_vector_constructs_inverse_coordinate_matrices v hv (Fin.last 3)
  exact ⟨T, S, hTS, hST, hcol,
    rationalImageNormal_conjugate_fixed_axis_of_common_vertex T S hTS hST H I v hcol hnormal⟩

end DimensionFourDependence
