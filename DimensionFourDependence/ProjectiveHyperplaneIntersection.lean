import DimensionFourDependence.HomogeneousSectionMultiplication

/-! # Positive-dimensional projective support meets every hyperplane -/

namespace DimensionFourDependence

open MvPolynomial Module Topology TopologicalSpace

attribute [local instance] MvPolynomial.gradedAlgebra

set_option maxHeartbeats 2000000

variable {K σ : Type*} [Field K] [Finite σ]

/-- Linear lower Hilbert growth forces every homogeneous linear
section to vanish somewhere on the actual projective support.
The proof uses eventual graded vanishing and quotient multiplication. -/
theorem projective_hyperplane_meets_support_of_hilbert_lower_bound
    (I : Ideal (MvPolynomial σ K))
    (hI : I.IsHomogeneous (homogeneousSubmodule σ K))
    (hlower : ∀ n : ℕ, n + 1 ≤ projectiveHilbertFunction I n)
    (L : MvPolynomial σ K) (hL : L.IsHomogeneous 1) :
    ∃ z : ProjectiveSpectrum (homogeneousSubmodule σ K),
      I ≤ z.asHomogeneousIdeal.toIdeal ∧ L ∈ z.asHomogeneousIdeal := by
  classical
  by_contra hn
  have havoid (z : ProjectiveSpectrum (homogeneousSubmodule σ K))
      (hz : I ≤ z.asHomogeneousIdeal.toIdeal) : L ∉ z.asHomogeneousIdeal :=
    fun hLz => hn ⟨z, hz, hLz⟩
  have hJ : (I ⊔ Ideal.span ({L} : Set (MvPolynomial σ K))).IsHomogeneous
      (homogeneousSubmodule σ K) := by
    apply hI.sup
    apply Ideal.homogeneous_span
    intro P hP
    obtain rfl := Set.mem_singleton_iff.mp hP
    exact ⟨1, hL⟩
  obtain ⟨M, hM⟩ := projectiveHilbertFunction_eventually_zero_of_projective_zeroLocus_empty
    (I ⊔ Ideal.span ({L} : Set (MvPolynomial σ K))) hJ
    (projective_zeroLocus_add_equation_empty_of_support_avoids I L havoid)
  have hstep (k : ℕ) : projectiveHilbertFunction I (M + k + 1) ≤
      projectiveHilbertFunction I (M + k) := by
    have hs := homogeneousQuotientSectionMultiplication_surjective I hI L hL (M + k)
      (hM (M + k + 1) (by omega))
    exact LinearMap.finrank_le_finrank_of_surjective hs
  have hbound (k : ℕ) : projectiveHilbertFunction I (M + k) ≤ projectiveHilbertFunction I M := by
    induction k with
    | zero => simp
    | succ k ih =>
      simpa only [Nat.add_assoc] using (hstep k).trans ih
  have hlo := hlower (M + projectiveHilbertFunction I M)
  have hup := hbound (projectiveHilbertFunction I M)
  omega

/-- A closed projective source map lifts the hyperplane intersection
to a specialization on the same given branch, without a chosen point
or a supplied nonempty fiber. -/
theorem closed_projective_branch_meets_hyperplane
    {X : Type*} [TopologicalSpace X]
    (f : X → ProjectiveSpectrum (homogeneousSubmodule σ K)) (hclosed : IsClosedMap f)
    (x : X)
    (hlower : ∀ n : ℕ, n + 1 ≤ projectiveHilbertFunction (f x).asHomogeneousIdeal.toIdeal n)
    (L : MvPolynomial σ K) (hL : L.IsHomogeneous 1) :
    ∃ z : X, x ⤳ z ∧ L ∈ (f z).asHomogeneousIdeal := by
  obtain ⟨p, hp, hLp⟩ := projective_hyperplane_meets_support_of_hilbert_lower_bound
    (f x).asHomogeneousIdeal.toIdeal (f x).asHomogeneousIdeal.isHomogeneous hlower L hL
  have hs : p ∈ closure {f x} := by
    rw [← ProjectiveSpectrum.zeroLocus_vanishingIdeal_eq_closure
      (homogeneousSubmodule σ K) {f x}, ProjectiveSpectrum.vanishingIdeal_singleton]
    exact hp
  obtain ⟨z, hz, he⟩ := hclosed.specializingMap.closure_singleton_subset x hs
  refine ⟨z, specializes_iff_mem_closure.mpr hz, ?_⟩
  rw [he]
  exact hLp

end DimensionFourDependence
