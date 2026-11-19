import DimensionFourDependence.PointAdaptedCoordinates
import DimensionFourDependence.LinearPolynomialCoordinates

/-! # An independent family supplies specified columns of inverse coordinate matrices -/

namespace DimensionFourDependence

open Matrix

set_option maxHeartbeats 2500000

variable {K : Type*} [Field K] {m n : ℕ}

/-- Extend an actual independent family to inverse original constant
coordinate matrices with the prescribed columns. This uses the exact
family vectors, without rescaling their projective representatives. -/
theorem independent_vector_family_constructs_inverse_coordinate_columns
    (v : Fin m → (Fin n → K)) (hv : LinearIndependent K v)
    (e : Fin m ↪ Fin n) :
    ∃ T S : Matrix (Fin n) (Fin n) K,
      T * S = 1 ∧ S * T = 1 ∧ ∀ i j, T j (e i) = v i j := by
  classical
  let w : Fin m → (Fin n → K) := fun i => Pi.single (e i) 1
  have hw : LinearIndependent K w := (Pi.linearIndependent_single_one (Fin n) K).comp e e.injective
  let ev := hv.linearCombinationEquiv
  let ew := hw.linearCombinationEquiv
  let f := ew.symm.trans ev
  obtain ⟨g, hg⟩ := Submodule.exists_linearEquiv_restrict_eq f
  have hsend (i : Fin m) : g (w i) = v i := by
    have he := hg (ew (Finsupp.single i 1))
    have hf : f (ew (Finsupp.single i 1)) = ev (Finsupp.single i 1) := by simp [f]
    rw [hf] at he
    simpa only [ev, ew, LinearIndependent.linearCombinationEquiv_apply_coe,
      Finsupp.linearCombination_single, one_smul] using he.symm
  let T := LinearMap.toMatrix' g.toLinearMap
  let S := LinearMap.toMatrix' g.symm.toLinearMap
  have hTS : T * S = 1 := by
    rw [← LinearMap.toMatrix'_comp]
    have heq : g.toLinearMap.comp g.symm.toLinearMap = LinearMap.id := by
      apply LinearMap.ext
      intro x
      exact g.apply_symm_apply x
    rw [heq, LinearMap.toMatrix'_id]
  have hST : S * T = 1 := by
    rw [← LinearMap.toMatrix'_comp]
    have heq : g.symm.toLinearMap.comp g.toLinearMap = LinearMap.id := by
      apply LinearMap.ext
      intro x
      exact g.symm_apply_apply x
    rw [heq, LinearMap.toMatrix'_id]
  have hTv (i) : T *ᵥ w i = v i := by
    change Matrix.toLin' (LinearMap.toMatrix' g.toLinearMap) (w i) = _
    rw [Matrix.toLin'_toMatrix']
    exact hsend i
  refine ⟨T, S, hTS, hST, ?_⟩
  intro i j
  have he := congrFun (hTv i) j
  simpa only [w, Matrix.mulVec_single_one, Matrix.col_apply] using he

end DimensionFourDependence
