import DimensionFourDependence.HilbertPolynomialExistence
import Mathlib.RingTheory.GradedAlgebra.Radical
import Mathlib.RingTheory.Finiteness.Ideal

/-! # Empty projective support forces eventual graded vanishing

A homogeneous ideal with no relevant homogeneous prime contains a
power of the ideal of all variables. Thus its actual homogeneous
quotient pieces vanish in every sufficiently large degree. This also
applies when cutting a finite projective support by an equation which
is nonzero at every point of that support.
-/

namespace DimensionFourDependence

open MvPolynomial Module

attribute [local instance] MvPolynomial.gradedAlgebra

variable {F sigma : Type*} [Field F]

/-- Empty projective support puts every variable in the radical of
the actual homogeneous ideal, using homogeneous cores of arbitrary primes. -/
theorem idealOfVars_le_radical_of_projective_zeroLocus_empty
    (I : Ideal (MvPolynomial sigma F))
    (hI : I.IsHomogeneous (homogeneousSubmodule sigma F))
    (hempty : ProjectiveSpectrum.zeroLocus (homogeneousSubmodule sigma F) (I : Set _) = ∅) :
    idealOfVars sigma F ≤ I.radical := by
  rw [Ideal.radical_eq_sInf]
  apply le_sInf
  intro P hP
  have hcore : HomogeneousIdeal.irrelevant (homogeneousSubmodule sigma F) ≤
      P.homogeneousCore (homogeneousSubmodule sigma F) := by
    by_contra hrel
    let z : ProjectiveSpectrum (homogeneousSubmodule sigma F) :=
      ⟨P.homogeneousCore _, hP.2.homogeneousCore, hrel⟩
    have hz : z ∈ ProjectiveSpectrum.zeroLocus (homogeneousSubmodule sigma F) (I : Set _) := by
      change I ≤ (P.homogeneousCore (homogeneousSubmodule sigma F)).toIdeal
      exact hI.toIdeal_homogeneousCore_eq_self.symm.trans_le
        (Ideal.homogeneousCore_mono _ hP.1)
    rw [hempty] at hz
    exact Set.notMem_empty z hz
  apply Ideal.span_le.mpr
  rintro _ ⟨i, rfl⟩
  exact P.toIdeal_homogeneousCore_le _ (hcore
    (HomogeneousIdeal.mem_irrelevant_of_mem _ (show 0 < (1 : ℕ) by omega)
      (isHomogeneous_X (R := F) i)))

/-- A power of the variable ideal makes all actual quotient pieces
of at least that degree zero. -/
theorem projectiveHilbertFunction_zero_of_variable_ideal_power_le
    [Finite sigma] (I : Ideal (MvPolynomial sigma F)) (N : ℕ)
    (hN : idealOfVars sigma F ^ N ≤ I) (n : ℕ) (hn : N ≤ n) :
    projectiveHilbertFunction I n = 0 := by
  have hrel : homogeneousRelationSpace I n = ⊤ := by
    apply top_unique
    intro p _
    change (p : MvPolynomial sigma F) ∈ I
    apply hN
    apply (mem_pow_idealOfVars_iff N (p : MvPolynomial sigma F)).mpr
    intro m hm
    have he : Finsupp.degree m = n := by
      simpa only [Finsupp.degree_apply] using (p.property.degree_eq_sum_deg_support hm).symm
    omega
  have hi := projectiveHilbertFunction_add_relation_finrank I n
  rw [hrel, finrank_top] at hi
  omega

/-- The actual Hilbert function vanishes eventually when the
homogeneous ideal has empty projective support. -/
theorem projectiveHilbertFunction_eventually_zero_of_projective_zeroLocus_empty
    [Finite sigma] (I : Ideal (MvPolynomial sigma F))
    (hI : I.IsHomogeneous (homogeneousSubmodule sigma F))
    (hempty : ProjectiveSpectrum.zeroLocus (homogeneousSubmodule sigma F) (I : Set _) = ∅) :
    ∃ N : ℕ, ∀ n ≥ N, projectiveHilbertFunction I n = 0 := by
  obtain ⟨N, hN⟩ := Ideal.exists_pow_le_of_le_radical_of_fg
    (idealOfVars_le_radical_of_projective_zeroLocus_empty I hI hempty)
    (idealOfVars sigma F).fg_of_isNoetherianRing
  exact ⟨N, projectiveHilbertFunction_zero_of_variable_ideal_power_le I N hN⟩

/-- A hypersurface avoiding every point of the actual projective
support has empty intersection with that support. -/
theorem projective_zeroLocus_add_equation_empty_of_support_avoids
    (I : Ideal (MvPolynomial sigma F)) (S : MvPolynomial sigma F)
    (hS : ∀ z : ProjectiveSpectrum (homogeneousSubmodule sigma F),
      I ≤ z.asHomogeneousIdeal.toIdeal → S ∉ z.asHomogeneousIdeal) :
    ProjectiveSpectrum.zeroLocus (homogeneousSubmodule sigma F)
      ((I ⊔ Ideal.span ({S} : Set (MvPolynomial sigma F)) : Ideal (MvPolynomial sigma F)) : Set _) = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro z hz
  apply hS z (fun P hP => hz ((show I ≤ I ⊔ Ideal.span {S} from le_sup_left) hP))
  exact hz ((show Ideal.span {S} ≤ I ⊔ Ideal.span {S} from le_sup_right)
    (Ideal.subset_span (by simp)))

end DimensionFourDependence
