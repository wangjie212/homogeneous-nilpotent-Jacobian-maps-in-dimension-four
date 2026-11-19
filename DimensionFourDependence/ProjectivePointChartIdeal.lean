import DimensionFourDependence.ExtensionFieldProjectivePoint
import DimensionFourDependence.AffinePrincipalCone

/-! # The entire projective point ideal on a normalized affine chart

Nonzero common scaling and coordinate reindexing preserve all homogeneous
relations. An actual principal affine-chart closure consequently supplies
the entire original projective relation ideal, not merely one equation.
-/

namespace DimensionFourDependence

open MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra

variable {K F σ τ : Type*} [Field K] [Field F] [Algebra K F]

/-- Membership retains the evaluations of every homogeneous component. -/
theorem projectiveFieldPointIdeal_mem_iff_components (A : σ → F)
    (P : MvPolynomial σ K) :
    P ∈ (projectiveFieldPointIdeal (E := K) A).toIdeal ↔
      ∀ d : ℕ, aeval A (homogeneousComponent d P) = 0 := by
  change projectiveFieldPointMap A P = 0 ↔ _
  constructor
  · intro h d
    rw [← projectiveFieldPointMap_coeff, h, Polynomial.coeff_zero]
  · intro h
    apply Polynomial.ext
    intro d
    rw [projectiveFieldPointMap_coeff, h d, Polynomial.coeff_zero]

/-- For a homogeneous form, ideal membership is its actual value zero. -/
theorem projectiveFieldPointIdeal_mem_homogeneous (A : σ → F)
    (P : MvPolynomial σ K) {d : ℕ} (hP : P.IsHomogeneous d) :
    P ∈ (projectiveFieldPointIdeal (E := K) A).toIdeal ↔ aeval A P = 0 := by
  change projectiveFieldPointMap A P = 0 ↔ _
  rw [projectiveFieldPointMap_homogeneous A hP, Polynomial.monomial_eq_zero_iff]

/-- Nonzero common scaling preserves the entire actual relation ideal. -/
theorem projectiveFieldPointIdeal_scale (A : σ → F) (c : F) (hc : c ≠ 0) :
    (projectiveFieldPointIdeal (E := K) (fun i => c * A i)).toIdeal =
      (projectiveFieldPointIdeal (E := K) A).toIdeal := by
  ext P
  rw [projectiveFieldPointIdeal_mem_iff_components, projectiveFieldPointIdeal_mem_iff_components]
  simp_rw [homogeneous_aeval_scale_indexed _ (homogeneousComponent_isHomogeneous _ _) A c,
    mul_eq_zero, pow_ne_zero _ hc, false_or]

/-- Renaming all original coordinates transports the entire relation ideal. -/
theorem projectiveFieldPointIdeal_reindex (A : σ → F) (r : σ ≃ τ) :
    (projectiveFieldPointIdeal (E := K) A).toIdeal =
      ((projectiveFieldPointIdeal (E := K) (A ∘ r.symm)).toIdeal).comap
        (renameEquiv K r).toRingHom := by
  ext P
  change P ∈ (projectiveFieldPointIdeal (E := K) A).toIdeal ↔
    rename r P ∈ (projectiveFieldPointIdeal (E := K) (A ∘ r.symm)).toIdeal
  rw [projectiveFieldPointIdeal_mem_iff_components, projectiveFieldPointIdeal_mem_iff_components]
  apply forall_congr'
  intro d
  rw [← rename_homogeneousComponent, aeval_rename]
  simp only [Function.comp_def, Equiv.symm_apply_apply]

/-- A normalized chart and its projective cone have exactly the
original projective relation ideal in the original coordinates. -/
theorem projectiveFieldPointIdeal_eq_chart_comap
    (A : σ → F) (r : σ ≃ Option τ) (hj : A (r.symm none) ≠ 0) :
    (projectiveFieldPointIdeal (E := K) A).toIdeal =
      (projectiveConeIdeal (L := K)
        (fun i => A (r.symm (some i)) / A (r.symm none))).comap
          (renameEquiv K r).toRingHom := by
  rw [projectiveFieldPointIdeal_reindex A r]
  congr 1
  let x : τ → F := fun i => A (r.symm (some i)) / A (r.symm none)
  have hp : (fun i : Option τ => A (r.symm none) * i.elim 1 x) = A ∘ r.symm := by
    funext i
    cases i with
    | none => simp
    | some i => exact mul_div_cancel₀ _ hj
  have he := projectiveFieldPointIdeal_scale (K := K)
    (fun i : Option τ => i.elim 1 x) (A (r.symm none)) hj
  rw [hp] at he
  exact he

end DimensionFourDependence
