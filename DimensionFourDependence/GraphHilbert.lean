import DimensionFourDependence.ProjectiveGraph

/-! # Hilbert functions are preserved by graph hyperplanes and coordinate reindexing -/

namespace DimensionFourDependence

open MvPolynomial Module

variable {L F σ τ : Type*} [Field L] [Field F] [Algebra L F]

/-- Evaluation on the affine chart, restricted to a homogeneous polynomial piece. -/
noncomputable def homogeneousChartEvaluation (x : σ → F) (d : ℕ) :
    homogeneousSubmodule (Option σ) L d →ₗ[L] F :=
  (aeval (fun j : Option σ => j.elim 1 x)).toLinearMap.comp
    (homogeneousSubmodule (Option σ) L d).subtype

theorem homogeneousChartEvaluation_ker (x : σ → F) (d : ℕ) :
    LinearMap.ker (homogeneousChartEvaluation (L := L) x d) =
      homogeneousRelationSpace (projectiveConeIdeal (L := L) x) d := by
  ext p
  change aeval (fun j : Option σ => j.elim 1 x) (p : MvPolynomial (Option σ) L) = 0 ↔
    (p : MvPolynomial (Option σ) L) ∈ projectiveConeIdeal (L := L) x
  exact (projectiveConeIdeal_mem_of_isHomogeneous x p.property).symm

theorem projectiveHilbertFunction_cone_eq_chart_rank (x : σ → F) (d : ℕ) :
    projectiveHilbertFunction (projectiveConeIdeal (L := L) x) d =
      finrank L (LinearMap.range (homogeneousChartEvaluation (L := L) x d)) := by
  unfold projectiveHilbertFunction
  rw [← homogeneousChartEvaluation_ker]
  exact (homogeneousChartEvaluation (L := L) x d).quotKerEquivRange.finrank_eq

variable {n : ℕ}

/-- An affine graph hyperplane preserves every value of the projective Hilbert function. -/
theorem projectiveHilbertFunction_graph (c : L) (a : Fin n → L) (x : Fin n → F) (d : ℕ) :
    projectiveHilbertFunction (projectiveConeIdeal (L := L) (affineGraphPoint c a x)) d =
      projectiveHilbertFunction (projectiveConeIdeal (L := L) x) d := by
  have he : homogeneousChartEvaluation (L := L) (affineGraphPoint c a x) d =
      (homogeneousChartEvaluation (L := L) x d).comp (homogeneousGraphPullback c a d) := by
    apply LinearMap.ext
    intro p
    exact projectiveGraphPullback_aeval c a x p
  rw [projectiveHilbertFunction_cone_eq_chart_rank, projectiveHilbertFunction_cone_eq_chart_rank, he]
  have hr := LinearMap.range_comp_of_range_eq_top (homogeneousChartEvaluation (L := L) x d)
    (LinearMap.range_eq_top.mpr (homogeneousGraphPullback_surjective c a d))
  rw [hr]

/-- The graph embedding preserves the positive integral projective Hilbert degree. -/
theorem curveHilbertDegree_graph (c : L) (a : Fin n → L) (x : Fin n → F) (e : ℕ) :
    HasCurveHilbertDegree (projectiveConeIdeal (L := L) (affineGraphPoint c a x)) e ↔
      HasCurveHilbertDegree (projectiveConeIdeal (L := L) x) e := by
  simp only [HasCurveHilbertDegree, projectiveHilbertFunction_graph]

/-- Coordinate reindexing is a linear isomorphism on every homogeneous piece. -/
noncomputable def homogeneousRenameEquiv (e : σ ≃ τ) (d : ℕ) :
    homogeneousSubmodule σ L d ≃ₗ[L] homogeneousSubmodule τ L d where
  toFun p := ⟨rename e (p : MvPolynomial σ L), p.property.rename_isHomogeneous⟩
  invFun p := ⟨rename e.symm (p : MvPolynomial τ L), p.property.rename_isHomogeneous⟩
  left_inv p := Subtype.ext ((renameEquiv L e).symm_apply_apply p)
  right_inv p := Subtype.ext ((renameEquiv L e).apply_symm_apply p)
  map_add' p q := Subtype.ext ((renameEquiv L e).map_add p q)
  map_smul' r p := Subtype.ext ((renameEquiv L e).toLinearEquiv.map_smul r p)

/-- Reordering source coordinates preserves the Hilbert function of their projective closure. -/
theorem projectiveHilbertFunction_reindex (e : σ ≃ τ) (x : τ → F) (d : ℕ) :
    projectiveHilbertFunction (projectiveConeIdeal (L := L) (x ∘ e)) d =
      projectiveHilbertFunction (projectiveConeIdeal (L := L) x) d := by
  let eH := homogeneousRenameEquiv (L := L) e.optionCongr d
  have he : homogeneousChartEvaluation (L := L) (x ∘ e) d =
      (homogeneousChartEvaluation (L := L) x d).comp eH.toLinearMap := by
    apply LinearMap.ext
    intro p
    change aeval (fun j : Option σ => j.elim 1 (x ∘ e)) (p : MvPolynomial (Option σ) L) =
      aeval (fun j : Option τ => j.elim 1 x) (rename e.optionCongr (p : MvPolynomial (Option σ) L))
    rw [MvPolynomial.aeval_rename]
    have hpoint : (fun j : Option σ => j.elim 1 (x ∘ e)) =
        (fun j : Option τ => j.elim 1 x) ∘ e.optionCongr := by
      funext j
      cases j <;> rfl
    rw [hpoint]
  rw [projectiveHilbertFunction_cone_eq_chart_rank, projectiveHilbertFunction_cone_eq_chart_rank, he]
  have hr := LinearMap.range_comp_of_range_eq_top
    (homogeneousChartEvaluation (L := L) x d) (LinearMap.range_eq_top.mpr eH.surjective)
  rw [hr]

theorem curveHilbertDegree_reindex (e : σ ≃ τ) (x : τ → F) (d : ℕ) :
    HasCurveHilbertDegree (projectiveConeIdeal (L := L) (x ∘ e)) d ↔
      HasCurveHilbertDegree (projectiveConeIdeal (L := L) x) d := by
  simp only [HasCurveHilbertDegree, projectiveHilbertFunction_reindex]

end DimensionFourDependence
