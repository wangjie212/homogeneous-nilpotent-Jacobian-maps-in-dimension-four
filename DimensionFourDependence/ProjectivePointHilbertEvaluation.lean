import DimensionFourDependence.ProjectivePointChartIdeal
import DimensionFourDependence.ProjectiveHilbert

/-! # Projective Hilbert functions are spans of actual degree monomial values -/

namespace DimensionFourDependence

open MvPolynomial Module

attribute [local instance] MvPolynomial.gradedAlgebra

variable {K F σ : Type*} [Field K] [Field F] [Algebra K F]

/-- Evaluation of one homogeneous polynomial piece at the original
projective coordinate vector, with no affine chart chosen. -/
noncomputable def homogeneousPointEvaluation (x : σ → F) (d : ℕ) :
    homogeneousSubmodule σ K d →ₗ[K] F :=
  (aeval x).toLinearMap.comp (homogeneousSubmodule σ K d).subtype

/-- The exact homogeneous relation space is the kernel of evaluation. -/
theorem homogeneousPointEvaluation_ker (x : σ → F) (d : ℕ) :
    LinearMap.ker (homogeneousPointEvaluation (K := K) x d) =
      homogeneousRelationSpace (projectiveFieldPointIdeal (E := K) x).toIdeal d := by
  ext P
  change aeval x (P : MvPolynomial σ K) = 0 ↔ (P : MvPolynomial σ K) ∈
    (projectiveFieldPointIdeal (E := K) x).toIdeal
  exact (projectiveFieldPointIdeal_mem_homogeneous x (P : MvPolynomial σ K) P.property).symm

/-- The entire projective point ideal has the Hilbert function of
the actual homogeneous evaluation range. -/
theorem projectiveHilbertFunction_point_eq_evaluation_rank (x : σ → F) (d : ℕ) :
    projectiveHilbertFunction (projectiveFieldPointIdeal (E := K) x).toIdeal d =
      finrank K (LinearMap.range (homogeneousPointEvaluation (K := K) x d)) := by
  unfold projectiveHilbertFunction
  rw [← homogeneousPointEvaluation_ker]
  exact (homogeneousPointEvaluation (K := K) x d).quotKerEquivRange.finrank_eq

/-- Degree monomials with coefficient one generate exactly the
homogeneous evaluation range over the original coefficient field. -/
theorem homogeneousPointEvaluation_range_eq_monomial_span (x : σ → F) (d : ℕ) :
    LinearMap.range (homogeneousPointEvaluation (K := K) x d) =
      Submodule.span K (Set.range (fun m : {m : σ →₀ ℕ // m.degree = d} =>
        m.val.prod (fun i n => x i ^ n))) := by
  classical
  apply le_antisymm
  · rintro _ ⟨P, rfl⟩
    change aeval x (P : MvPolynomial σ K) ∈ _
    rw [(P : MvPolynomial σ K).as_sum, map_sum]
    apply Submodule.sum_mem
    intro m hm
    have hdegree : m.degree = d := by
      simpa only [Finsupp.degree_apply] using (P.property.degree_eq_sum_deg_support hm).symm
    have hmono : m.prod (fun i n => x i ^ n) ∈
        Submodule.span K (Set.range (fun s : {m : σ →₀ ℕ // m.degree = d} =>
          s.val.prod (fun i n => x i ^ n))) := Submodule.subset_span ⟨⟨m, hdegree⟩, rfl⟩
    simpa only [aeval_monomial, Algebra.smul_def] using
      (Submodule.span K (Set.range (fun s : {m : σ →₀ ℕ // m.degree = d} =>
        s.val.prod (fun i n => x i ^ n)))).smul_mem (P.val.coeff m) hmono
  · apply Submodule.span_le.mpr
    rintro _ ⟨m, rfl⟩
    refine ⟨⟨monomial m.val 1, isHomogeneous_monomial 1 m.property⟩, ?_⟩
    change aeval x (monomial m.val (1 : K)) = _
    simp only [aeval_monomial, map_one, one_mul]

/-- Every projective Hilbert function value is the dimension of the
span of the original degree monomial values in the given field. -/
theorem projectiveHilbertFunction_point_eq_monomial_span_finrank (x : σ → F) (d : ℕ) :
    projectiveHilbertFunction (projectiveFieldPointIdeal (E := K) x).toIdeal d =
      finrank K (Submodule.span K (Set.range (fun m : {m : σ →₀ ℕ // m.degree = d} =>
        m.val.prod (fun i n => x i ^ n)))) := by
  rw [projectiveHilbertFunction_point_eq_evaluation_rank,
    homogeneousPointEvaluation_range_eq_monomial_span]

end DimensionFourDependence
