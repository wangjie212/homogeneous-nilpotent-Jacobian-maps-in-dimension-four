import DimensionFourDependence.HomogeneousBaseChange

/-! # Hilbert functions are unchanged by a field extension

The quotient map restricted to a homogeneous piece has the same rank
after scalar extension. The canonical tensor isomorphisms identify this
map with the quotient map for the extended polynomial ideal.
-/

namespace DimensionFourDependence

open MvPolynomial TensorProduct Module

variable {L : Type*} [Field L] (E : Type*) [Field E] [Algebra L E] {σ : Type*}

/-- The quotient map restricted to one homogeneous polynomial piece. -/
noncomputable def homogeneousQuotientProjection (I : Ideal (MvPolynomial σ L)) (d : ℕ) :
    homogeneousSubmodule σ L d →ₗ[L] MvPolynomial σ L ⧸ I :=
  (Ideal.Quotient.mkₐ L I).toLinearMap.comp (homogeneousSubmodule σ L d).subtype

theorem homogeneousQuotientProjection_ker (I : Ideal (MvPolynomial σ L)) (d : ℕ) :
    LinearMap.ker (homogeneousQuotientProjection I d) = homogeneousRelationSpace I d := by
  ext p
  change Ideal.Quotient.mk I (p : MvPolynomial σ L) = 0 ↔ (p : MvPolynomial σ L) ∈ I
  exact Ideal.Quotient.eq_zero_iff_mem

/-- The Hilbert function is the rank of this restricted quotient map. -/
theorem projectiveHilbertFunction_eq_projection_rank (I : Ideal (MvPolynomial σ L)) (d : ℕ) :
    projectiveHilbertFunction I d = finrank L (LinearMap.range (homogeneousQuotientProjection I d)) := by
  unfold projectiveHilbertFunction
  rw [← homogeneousQuotientProjection_ker]
  exact (homogeneousQuotientProjection I d).quotKerEquivRange.finrank_eq

/-- The restricted quotient maps commute with the canonical scalar-extension isomorphisms. -/
theorem homogeneousQuotientProjection_baseChange (I : Ideal (MvPolynomial σ L)) (d : ℕ) :
    (homogeneousQuotientProjection (extendCoefficientIdeal E I) d).comp
        (homogeneousBaseChangeEquiv (L := L) E d).toLinearMap =
      (polynomialQuotientBaseChangeEquiv E I).toLinearMap.comp
        ((homogeneousQuotientProjection I d).baseChange E) := by
  apply LinearMap.ext
  intro z
  induction z using TensorProduct.inductionOn with
  | add z w hz hw => simp only [map_add, hz, hw]
  | tmul a p =>
    change Ideal.Quotient.mk (extendCoefficientIdeal E I)
      (homogeneousBaseChangeEquiv E d (a ⊗ₜ[L] p) : MvPolynomial σ E) =
        polynomialQuotientBaseChangeEquiv E I (a ⊗ₜ[L] Ideal.Quotient.mk I (p : MvPolynomial σ L))
    rw [polynomialQuotientBaseChangeEquiv_tmul, homogeneousBaseChangeEquiv_tmul]
    exact (Ideal.Quotient.mkₐ E _).toLinearMap.map_smul a _

/-- Extending the coefficient field preserves every value of the Hilbert function. -/
theorem projectiveHilbertFunction_field_extension [Finite σ]
    (I : Ideal (MvPolynomial σ L)) (d : ℕ) :
    projectiveHilbertFunction (extendCoefficientIdeal E I) d = projectiveHilbertFunction I d := by
  rw [projectiveHilbertFunction_eq_projection_rank, projectiveHilbertFunction_eq_projection_rank]
  have he := congrArg (fun f => finrank E (LinearMap.range f))
    (homogeneousQuotientProjection_baseChange E I d)
  rw [LinearMap.range_comp (homogeneousBaseChangeEquiv (L := L) E d).toLinearMap
      (homogeneousQuotientProjection (extendCoefficientIdeal E I) d),
    LinearMap.range_comp ((homogeneousQuotientProjection I d).baseChange E)
      (polynomialQuotientBaseChangeEquiv E I).toLinearMap] at he
  rw [show LinearMap.range (homogeneousBaseChangeEquiv (L := L) (σ := σ) E d).toLinearMap = ⊤ from
    LinearMap.range_eq_top.mpr (homogeneousBaseChangeEquiv E d).surjective, Submodule.map_top] at he
  have hmap : finrank E ((LinearMap.range ((homogeneousQuotientProjection I d).baseChange E)).map
      (polynomialQuotientBaseChangeEquiv E I).toLinearMap) =
      finrank E (LinearMap.range ((homogeneousQuotientProjection I d).baseChange E)) :=
    (polynomialQuotientBaseChangeEquiv E I).toLinearEquiv.finrank_map_eq _
  rw [hmap, scalarExtension_range_finrank] at he
  exact he

/-- In particular, a positive integral Hilbert degree is preserved by every field extension. -/
theorem curveHilbertDegree_field_extension [Finite σ]
    (I : Ideal (MvPolynomial σ L)) (e : ℕ) (he : HasCurveHilbertDegree I e) :
    HasCurveHilbertDegree (extendCoefficientIdeal E I) e := by
  obtain ⟨he, b, N, hN⟩ := he
  refine ⟨he, b, N, ?_⟩
  intro n hn
  rw [projectiveHilbertFunction_field_extension]
  exact hN n hn

end DimensionFourDependence
