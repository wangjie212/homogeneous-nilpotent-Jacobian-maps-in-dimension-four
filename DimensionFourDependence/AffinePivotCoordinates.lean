import DimensionFourDependence.AffineSubstitutionDegree

/-! # An affine hyperplane can replace one of the original coordinates

A nonzero pivot coefficient supplies an invertible affine substitution.
Its inverse preserves nonzero equations and does not increase their total
degree, so the original hypersurface bound also applies to linear sections.
-/

namespace DimensionFourDependence

open MvPolynomial

set_option maxHeartbeats 1000000

variable {k σ : Type*} [Field k] [Fintype σ] [DecidableEq σ]

/-- The constant and nonpivot part of the actual affine linear form. -/
noncomputable def affinePivotRemainder (j : σ) (b : k) (c : σ → k) : MvPolynomial σ k :=
  C b + ∑ i ∈ Finset.univ.erase j, C (c i) * X i

/-- Replace the pivot variable by its actual affine linear form. -/
noncomputable def affinePivotSubstitution (j : σ) (a b : k) (c : σ → k) :
    MvPolynomial σ k →ₐ[k] MvPolynomial σ k :=
  aeval (fun i => if i = j then C a * X j + affinePivotRemainder j b c else X i)

/-- Solve the affine linear form for the original pivot coordinate. -/
noncomputable def affinePivotInverseSubstitution (j : σ) (a b : k) (c : σ → k) :
    MvPolynomial σ k →ₐ[k] MvPolynomial σ k :=
  aeval (fun i => if i = j then C a⁻¹ * (X j - affinePivotRemainder j b c) else X i)

/-- A substitution fixing the nonpivot variables fixes the remainder. -/
theorem affinePivotRemainder_fixed (j : σ) (b : k) (c : σ → k)
    (g : MvPolynomial σ k →ₐ[k] MvPolynomial σ k)
    (hg : ∀ i, i ≠ j → g (X i) = X i) :
    g (affinePivotRemainder j b c) = affinePivotRemainder j b c := by
  simp only [affinePivotRemainder, map_add, map_sum, map_mul, algHom_C, algebraMap_eq]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  rw [hg i (Finset.mem_erase.mp hi).1]

/-- The forward affine substitution fixes the entire nonpivot remainder. -/
theorem affinePivotSubstitution_remainder (j : σ) (a b : k) (c : σ → k) :
    affinePivotSubstitution j a b c (affinePivotRemainder j b c) = affinePivotRemainder j b c := by
  apply affinePivotRemainder_fixed
  intro i hi
  simp [affinePivotSubstitution, hi]

/-- Substituting the affine form after solving for the pivot recovers
every original polynomial exactly. -/
theorem affinePivotSubstitution_comp_inverse
    (j : σ) (a b : k) (c : σ → k) (ha : a ≠ 0) :
    (affinePivotSubstitution j a b c).comp (affinePivotInverseSubstitution j a b c) =
      AlgHom.id k _ := by
  let F := affinePivotSubstitution j a b c
  let G := affinePivotInverseSubstitution j a b c
  change F.comp G = AlgHom.id k _
  apply MvPolynomial.algHom_ext
  intro i
  simp only [AlgHom.comp_apply, AlgHom.id_apply]
  by_cases hi : i = j
  · subst i
    simp only [G, affinePivotInverseSubstitution, aeval_X, ite_true]
    rw [map_mul, map_sub, algHom_C, algebraMap_eq, affinePivotSubstitution_remainder]
    simp only [F, affinePivotSubstitution, aeval_X, ite_true]
    rw [add_sub_cancel_right, ← mul_assoc, ← map_mul, inv_mul_cancel₀ ha, map_one, one_mul]
  · simp [F, G, affinePivotSubstitution, affinePivotInverseSubstitution, hi]
  
/-- Solving for a pivot with nonzero coefficient preserves every nonzero
original equation: the inverse substitution is injective. -/
theorem affinePivotInverseSubstitution_injective
    (j : σ) (a b : k) (c : σ → k) (ha : a ≠ 0) :
    Function.Injective (affinePivotInverseSubstitution j a b c) := by
  have hcomp := affinePivotSubstitution_comp_inverse j a b c ha
  intro f g hfg
  have h := congrArg (affinePivotSubstitution j a b c) hfg
  have hf := AlgHom.congr_fun hcomp f
  have hg := AlgHom.congr_fun hcomp g
  exact hf.symm.trans (h.trans hg)

/-- The nonpivot part of an affine linear form has degree at most one. -/
theorem affinePivotRemainder_totalDegree_le
    (j : σ) (b : k) (c : σ → k) : (affinePivotRemainder j b c).totalDegree ≤ 1 := by
  apply (totalDegree_add _ _).trans
  apply max_le (by simp)
  apply totalDegree_finsetSum_le
  intro i _
  exact (totalDegree_mul _ _).trans (by simp)

/-- The inverse affine pivot substitution does not increase the degree
of the original hypersurface equation. -/
theorem affinePivotInverseSubstitution_totalDegree_le
    (j : σ) (a b : k) (c : σ → k) (f : MvPolynomial σ k) :
    (affinePivotInverseSubstitution j a b c f).totalDegree ≤ f.totalDegree := by
  apply totalDegree_aeval_le_of_affine
  intro i
  by_cases hi : i = j
  · simp only [if_pos hi]
    apply (totalDegree_mul _ _).trans
    simp only [totalDegree_C, zero_add]
    exact (totalDegree_sub _ _).trans (max_le (by simp) (affinePivotRemainder_totalDegree_le j b c))
  · simp [hi]

end DimensionFourDependence
