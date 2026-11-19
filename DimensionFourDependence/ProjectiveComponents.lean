import DimensionFourDependence.ProjectiveFiberPrime

/-! # Irreducible components in the projective spectrum

The homogeneous relation ideal defines an actual point of Mathlib's `Proj`.
Its closure is a maximal irreducible subset of the two-equation zero locus.
-/

namespace DimensionFourDependence

open MvPolynomial Topology

variable {A S : Type*} [CommRing A] [SetLike S A] [AddSubmonoidClass S A]
    (𝒜 : ℕ → S) [GradedRing 𝒜]

/-- An irreducible projective set has a prime vanishing ideal. -/
theorem projective_vanishingIdeal_isPrime {Z : Set (ProjectiveSpectrum 𝒜)} (hZ : IsIrreducible Z) :
    (ProjectiveSpectrum.vanishingIdeal Z).toIdeal.IsPrime := by
  refine ⟨?_, ?_⟩
  · intro he
    obtain ⟨z, hz⟩ := hZ.nonempty
    have h1 : (1 : A) ∈ (ProjectiveSpectrum.vanishingIdeal Z).toIdeal := by rw [he]; trivial
    have hz1 := (ProjectiveSpectrum.mem_vanishingIdeal Z 1).mp h1 z hz
    exact z.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hz1 isUnit_one)
  · intro f g hfg
    have hs : Z ⊆ ProjectiveSpectrum.zeroLocus 𝒜 {f} ∪ ProjectiveSpectrum.zeroLocus 𝒜 {g} := by
      rw [← ProjectiveSpectrum.zeroLocus_singleton_mul]
      intro z hz
      exact Set.singleton_subset_iff.mpr
        ((ProjectiveSpectrum.mem_vanishingIdeal Z (f * g)).mp hfg z hz)
    rcases isPreirreducible_iff_isClosed_union_isClosed.mp hZ.isPreirreducible _ _
        (ProjectiveSpectrum.isClosed_zeroLocus 𝒜 {f})
        (ProjectiveSpectrum.isClosed_zeroLocus 𝒜 {g}) hs with hf | hg
    · left
      apply (ProjectiveSpectrum.mem_vanishingIdeal Z f).mpr
      intro z hz
      exact hf hz (by simp)
    · right
      apply (ProjectiveSpectrum.mem_vanishingIdeal Z g).mpr
      intro z hz
      exact hg hz (by simp)

/-- A relevant homogeneous minimal prime gives a maximal irreducible
subset of the corresponding projective zero locus. -/
theorem projective_component_of_minimalPrime (p : ProjectiveSpectrum 𝒜) (s : Set A)
    (hp : p.asHomogeneousIdeal.toIdeal ∈ (Ideal.span s).minimalPrimes) :
    Maximal (fun Z : Set (ProjectiveSpectrum 𝒜) =>
      IsIrreducible Z ∧ Z ⊆ ProjectiveSpectrum.zeroLocus 𝒜 s) (closure {p}) := by
  have hc : ProjectiveSpectrum.zeroLocus 𝒜 (p.asHomogeneousIdeal : Set A) = closure {p} := by
    rw [← ProjectiveSpectrum.vanishingIdeal_singleton p]
    exact ProjectiveSpectrum.zeroLocus_vanishingIdeal_eq_closure 𝒜 {p}
  refine ⟨⟨isIrreducible_singleton.closure, ?_⟩, ?_⟩
  · apply closure_minimal _ (ProjectiveSpectrum.isClosed_zeroLocus 𝒜 s)
    exact Set.singleton_subset_iff.mpr (fun f hf => hp.le (Ideal.subset_span hf))
  · intro Z hZ hCZ
    let J := (ProjectiveSpectrum.vanishingIdeal Z).toIdeal
    have hJ : J.IsPrime := projective_vanishingIdeal_isPrime 𝒜 hZ.1
    have hspan : Ideal.span s ≤ J := by
      apply Ideal.span_le.mpr
      intro f hf
      exact (ProjectiveSpectrum.mem_vanishingIdeal Z f).mpr (fun z hz => hZ.2 hz hf)
    have hJP : J ≤ p.asHomogeneousIdeal.toIdeal := by
      intro f hf
      exact (ProjectiveSpectrum.mem_vanishingIdeal Z f).mp hf p
        (hCZ (subset_closure (by simp)))
    have hPJ := hp.2 ⟨hJ, hspan⟩ hJP
    have he : ProjectiveSpectrum.vanishingIdeal Z = p.asHomogeneousIdeal := by
      apply HomogeneousIdeal.toIdeal_injective
      exact le_antisymm hJP hPJ
    have hs := ProjectiveSpectrum.subset_zeroLocus_vanishingIdeal 𝒜 Z
    rw [he, hc] at hs
    exact hs

variable {L F σ : Type*} [Field L] [Field F] [Algebra L F]

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The cone relation ideal is homogeneous for the standard polynomial grading. -/
theorem projectiveConeIdeal_isHomogeneous (x : σ → F) :
    (projectiveConeIdeal (L := L) x).IsHomogeneous (homogeneousSubmodule (Option σ) L) := by
  intro d p hp
  change (MvPolynomial.decomposition.decompose' p d :
    MvPolynomial (Option σ) L) ∈ projectiveConeIdeal (L := L) x
  simpa only [MvPolynomial.decomposition.decompose'_apply] using
    projectiveConeIdeal_homogeneousComponent_mem x hp d

/-- The homogeneous ideal defining the actual projective closure. -/
noncomputable def projectiveClosureHomogeneousIdeal (x : σ → F) :
    HomogeneousIdeal (homogeneousSubmodule (Option σ) L) where
  toSubmodule := projectiveConeIdeal (L := L) x
  is_homogeneous' := projectiveConeIdeal_isHomogeneous x

/-- The generic point of the projective closure as a point of `Proj`. -/
noncomputable def projectiveClosureGenericPoint (x : σ → F) :
    ProjectiveSpectrum (homogeneousSubmodule (Option σ) L) where
  asHomogeneousIdeal := projectiveClosureHomogeneousIdeal (L := L) x
  isPrime := projectiveConeIdeal_isPrime x
  not_irrelevant_le := by
    intro h
    apply projectiveConeIdeal_X_none_not_mem (L := L) x
    exact h (HomogeneousIdeal.mem_irrelevant_of_mem _ (show 0 < (1 : ℕ) by omega)
      (isHomogeneous_X (R := L) (none : Option σ)))

/-- The projective closure, inside the actual projective spectrum. -/
noncomputable def projectiveClosureSet (x : σ → F) :
    Set (ProjectiveSpectrum (homogeneousSubmodule (Option σ) L)) :=
  closure {projectiveClosureGenericPoint (L := L) x}

theorem projectiveClosureSet_isIrreducible (x : σ → F) :
    IsIrreducible (projectiveClosureSet (L := L) x) := isIrreducible_singleton.closure

variable {K : Type*} [Field K] [CharZero K]

/-- The actual generic projective fiber is a maximal irreducible subset
of the intersection of the homogeneous quadratic and cubic equations. -/
theorem projective_fiber_witness_irreducible_component
    (H : Fin 4 → FractionRing (MvPolynomial (Fin 4) K))
    (hN : IsNilpotent (rationalJacobian H)) (hrank : (rationalJacobian H).rank = 3)
    (W : ProjectiveFiberEquationWitness H) :
    Maximal (fun Z => IsIrreducible Z ∧ Z ⊆
      ProjectiveSpectrum.zeroLocus (homogeneousSubmodule (Option (Fin 3))
        (coefficientField (K := K) (fun i : Fin 3 => H (W.affine.chart i.castSucc))))
          {W.quadric, W.cubic})
      (projectiveClosureSet
        (L := coefficientField (K := K) (fun i : Fin 3 => H (W.affine.chart i.castSucc)))
        (fun i : Fin 3 => rationalCoordinate (K := K) (W.affine.chart i.castSucc))) := by
  exact projective_component_of_minimalPrime _ _ _
    (projective_fiber_witness_prime_minimal_over_equations H hN hrank W)

end DimensionFourDependence
