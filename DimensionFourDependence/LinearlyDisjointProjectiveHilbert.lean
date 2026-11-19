import DimensionFourDependence.CurveCoefficientLinearDisjoint
import DimensionFourDependence.ProjectivePointHilbertEvaluation

/-! # Independent coefficient extension preserves the entire source-curve Hilbert function -/

namespace DimensionFourDependence

open Module MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000

variable {K C J F ι : Type*} [Field K] [Field C] [Field J] [Field F]
  [Algebra K C] [Algebra K J] [Algebra K F] [Algebra C F] [IsScalarTower K C F]

/-- If every original independent family remains independent, all
finite-dimensional original value spans preserve their dimension under
the specified compatible coefficient extension and source embedding. -/
theorem finite_span_finrank_eq_of_independence_preservation
    (f : J →ₐ[K] F) (v : ι → J)
    [Module.Finite K (Submodule.span K (Set.range v))]
    (hpreserve : ∀ {τ : Type} (w : τ → J), LinearIndependent K w →
      LinearIndependent C (f ∘ w)) :
    finrank C (Submodule.span C (Set.range (f ∘ v))) =
      finrank K (Submodule.span K (Set.range v)) := by
  classical
  let W := Submodule.span K (Set.range v)
  let V := Submodule.span C (Set.range (f ∘ v))
  let b := Module.finBasis K W
  let w := fun i => f (b i : J)
  let Vb := Submodule.span C (Set.range w)
  have hbK : LinearIndependent K (fun i => (b i : J)) :=
    b.linearIndependent.map' W.subtype (LinearMap.ker_eq_bot.mpr Subtype.val_injective)
  have hbC : LinearIndependent C w := hpreserve _ hbK
  have hW : W ≤ Submodule.comap f.toLinearMap (V.restrictScalars K) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact Submodule.subset_span ⟨i, rfl⟩
  have hle : Vb ≤ V := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact hW (b i).property
  let T : Submodule K W :=
    Submodule.comap (f.toLinearMap.comp W.subtype) (Vb.restrictScalars K)
  have hT : T = ⊤ := by
    apply top_unique
    rw [← b.span_eq]
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact Submodule.subset_span ⟨i, rfl⟩
  have hge : V ≤ Vb := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    have hi : (⟨v i, Submodule.subset_span (Set.mem_range_self i)⟩ : W) ∈ T := by
      rw [hT]
      trivial
    exact hi
  have he : V = Vb := le_antisymm hge hle
  change finrank C V = finrank K W
  rw [he]
  simpa only [Fintype.card_fin] using (finrank_span_eq_card hbC)

/-- Linear disjointness preserves every homogeneous projective
Hilbert function of a source curve in its original coordinates. -/
theorem projectiveHilbertFunction_point_eq_of_linearlyDisjoint
    (J : IntermediateField K F) (hdisj : J.LinearDisjoint C)
    {σ : Type*} [Finite σ] (x : σ → J) (n : ℕ) :
    projectiveHilbertFunction (projectiveFieldPointIdeal (E := C)
      (fun i => algebraMap J F (x i))).toIdeal n =
      projectiveHilbertFunction (projectiveFieldPointIdeal (E := K) x).toIdeal n := by
  let f := IsScalarTower.toAlgHom K J F
  let v := fun m : {m : σ →₀ ℕ // m.degree = n} => m.val.prod (fun i d => x i ^ d)
  letI : Module.Finite K (Submodule.span K (Set.range v)) := by
    change Module.Finite K (Submodule.span K (Set.range
      (fun m : {m : σ →₀ ℕ // m.degree = n} => m.val.prod (fun i d => x i ^ d))))
    rw [← homogeneousPointEvaluation_range_eq_monomial_span x n]
    infer_instance
  have he := finite_span_finrank_eq_of_independence_preservation (C := C) f v
    (fun {τ : Type} (w : τ → J) (hw : LinearIndependent K w) => hdisj.linearIndependent_left hw)
  have hv : f ∘ v = (fun m : {m : σ →₀ ℕ // m.degree = n} =>
      m.val.prod (fun i d => (algebraMap J F (x i)) ^ d)) := by
    funext m
    simp only [Function.comp_apply, v, Finsupp.prod, map_prod, map_pow]
    rfl
  rw [hv] at he
  simpa only [projectiveHilbertFunction_point_eq_monomial_span_finrank] using he

/-- Positive projective curve degree is unchanged by the same
linearly disjoint coefficient extension. -/
theorem projective_curve_degree_iff_of_linearlyDisjoint
    (J : IntermediateField K F) (hdisj : J.LinearDisjoint C)
    {σ : Type*} [Finite σ] (x : σ → J) (D : ℕ) :
    HasCurveHilbertDegree (projectiveFieldPointIdeal (E := C)
      (fun i => algebraMap J F (x i))).toIdeal D ↔
      HasCurveHilbertDegree (projectiveFieldPointIdeal (E := K) x).toIdeal D := by
  simp only [HasCurveHilbertDegree,
    projectiveHilbertFunction_point_eq_of_linearlyDisjoint J hdisj x]

end DimensionFourDependence
