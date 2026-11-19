import DimensionFourDependence.IndependentCovectorPairCoordinates

/-! # An independent pair can occupy any two specified frame rows -/

namespace DimensionFourDependence

open Matrix Module

set_option maxHeartbeats 2350000

variable {K : Type*} [Field K] {n : ℕ}

/-- Extend a linear equivalence of the two row spans to the whole
space and obtain actual inverse coordinate matrices. -/
theorem independent_covector_pair_constructs_specified_rows
    (v : Fin 2 → (Fin n → K)) (hv : LinearIndependent K v) (p : Fin 2 ↪ Fin n) :
    ∃ T S : Matrix (Fin n) (Fin n) K,
      T * S = 1 ∧ S * T = 1 ∧ ∀ i j, S (p i) j = v i j := by
  classical
  let w : Fin 2 → (Fin n → K) := fun i => Pi.single (p i) 1
  have hw : LinearIndependent K w :=
    (Pi.linearIndependent_single_one (Fin n) K).comp p p.injective
  let e := hv.linearCombinationEquiv
  let e' := hw.linearCombinationEquiv
  let f := e.symm.trans e'
  obtain ⟨g, hg⟩ := Submodule.exists_linearEquiv_restrict_eq f
  have hs (i : Fin 2) : g (v i) = w i := by
    have he := hg (e (Finsupp.single i 1))
    have hf : f (e (Finsupp.single i 1)) = e' (Finsupp.single i 1) := by simp [f]
    rw [hf] at he
    simpa only [e, e', LinearIndependent.linearCombinationEquiv_apply_coe,
      Finsupp.linearCombination_single, one_smul] using he.symm
  let A := LinearMap.toMatrix' g.toLinearMap
  let B := LinearMap.toMatrix' g.symm.toLinearMap
  have hAB : A * B = 1 := by
    rw [← LinearMap.toMatrix'_comp]
    have he : g.toLinearMap.comp g.symm.toLinearMap = LinearMap.id := by
      apply LinearMap.ext
      intro x
      exact g.apply_symm_apply x
    rw [he, LinearMap.toMatrix'_id]
  have hBA : B * A = 1 := by
    rw [← LinearMap.toMatrix'_comp]
    have he : g.symm.toLinearMap.comp g.toLinearMap = LinearMap.id := by
      apply LinearMap.ext
      intro x
      exact g.symm_apply_apply x
    rw [he, LinearMap.toMatrix'_id]
  refine ⟨Aᵀ, Bᵀ, ?_, ?_, ?_⟩
  · rw [← Matrix.transpose_mul, hBA, Matrix.transpose_one]
  · rw [← Matrix.transpose_mul, hAB, Matrix.transpose_one]
  · intro i j
    have hBi : B *ᵥ w i = v i := by
      change Matrix.toLin' (LinearMap.toMatrix' g.symm.toLinearMap) (w i) = _
      rw [Matrix.toLin'_toMatrix', ← hs]
      exact g.symm_apply_apply (v i)
    change B j (p i) = v i j
    simpa only [w, Matrix.mulVec_single_one, Matrix.col_apply] using congrFun hBi j

end DimensionFourDependence
