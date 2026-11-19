import DimensionFourDependence.DiscreteHilbertPolynomial

/-! # Existence of the Hilbert polynomial of a homogeneous quotient

Noetherian induction on the relation ideal uses the coordinate recurrence.
A strict colon ideal is covered by induction; a stable colon ideal gives
a first difference, which is integrated by Bernoulli polynomials.
-/

namespace DimensionFourDependence

open MvPolynomial Module

variable {L σ : Type*} [Field L] [Finite σ]

attribute [local instance] MvPolynomial.gradedAlgebra

/-- If every coordinate is a relation, all positive homogeneous pieces vanish. -/
theorem projectiveHilbertFunction_zero_of_variables_mem (I : Ideal (MvPolynomial σ L))
    (hX : ∀ i : σ, X i ∈ I) (n : ℕ) (hn : 0 < n) : projectiveHilbertFunction I n = 0 := by
  have hvars : idealOfVars σ L ≤ I := by
    apply Ideal.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact hX i
  have hrel : homogeneousRelationSpace I n = ⊤ := by
    apply top_unique
    intro p _
    change (p : MvPolynomial σ L) ∈ I
    apply hvars
    rw [← pow_one (idealOfVars σ L)]
    apply (mem_pow_idealOfVars_iff 1 (p : MvPolynomial σ L)).mpr
    intro m hm
    have he : Finsupp.degree m = n := by
      simpa only [Finsupp.degree_apply] using (p.property.degree_eq_sum_deg_support hm).symm
    omega
  have hi := projectiveHilbertFunction_add_relation_finrank I n
  rw [hrel, finrank_top] at hi
  omega

/-- Every homogeneous ideal in a polynomial ring over a field has an
eventual rational Hilbert polynomial for the actual homogeneous quotient. -/
theorem projectiveHilbertFunction_eventually_polynomial (I : Ideal (MvPolynomial σ L))
    (hI : I.IsHomogeneous (homogeneousSubmodule σ L)) :
    EventuallyPolynomialSequence (fun n => (projectiveHilbertFunction I n : ℚ)) := by
  classical
  refine IsNoetherian.induction
    (P := fun J : Ideal (MvPolynomial σ L) =>
      J.IsHomogeneous (homogeneousSubmodule σ L) →
        EventuallyPolynomialSequence (fun n => (projectiveHilbertFunction J n : ℚ))) ?_ I hI
  intro J ih hJ
  by_cases hX : ∀ i : σ, X i ∈ J
  · refine ⟨0, 1, ?_⟩
    intro n hn
    rw [Polynomial.eval_zero]
    change (0 : ℚ) = (projectiveHilbertFunction J n : ℚ)
    rw [projectiveHilbertFunction_zero_of_variables_mem J hX n (by omega)]
    exact Nat.cast_zero.symm
  · push Not at hX
    obtain ⟨i, hi⟩ := hX
    have hsup : J < J ⊔ Ideal.span ({X i} : Set (MvPolynomial σ L)) := by
      apply lt_of_le_of_ne le_sup_left
      intro he
      have hm : X i ∈ J ⊔ Ideal.span ({X i} : Set (MvPolynomial σ L)) :=
        (show Ideal.span {X i} ≤ J ⊔ Ideal.span {X i} from le_sup_right)
          (Ideal.subset_span (by simp))
      rw [← he] at hm
      exact hi hm
    have hsupPoly := ih _ hsup (sup_coordinate_isHomogeneous J hJ i)
    by_cases hc : J = coordinateColon J i
    · obtain ⟨p, N, hp⟩ := hsupPoly
      apply eventualPolynomial_of_difference (fun n => (projectiveHilbertFunction J n : ℚ)) p N
      intro n hn
      have hr := projectiveHilbertFunction_coordinate_recurrence J hJ i n
      rw [← hc] at hr
      have hcast := congrArg (fun a : ℕ => (a : ℚ)) hr
      push_cast at hcast
      have hv := hp (n + 1) (by omega)
      push_cast at hv
      linarith
    · have hcolon : J < coordinateColon J i := lt_of_le_of_ne (le_coordinateColon J i) hc
      have hcolonPoly := ih _ hcolon (coordinateColon_isHomogeneous J hJ i)
      apply eventualPolynomial_of_shifted_sum
        (fun n => (projectiveHilbertFunction J n : ℚ))
        (fun n => (projectiveHilbertFunction (coordinateColon J i) n : ℚ))
        (fun n => (projectiveHilbertFunction (J ⊔ Ideal.span {X i}) n : ℚ)) hcolonPoly hsupPoly
      intro n
      exact_mod_cast projectiveHilbertFunction_coordinate_recurrence J hJ i n

/-- The actual projective fiber closure has an eventual Hilbert polynomial. -/
theorem projectiveConeIdeal_hilbert_polynomial {F : Type*} [Field F] [Algebra L F] (x : σ → F) :
    EventuallyPolynomialSequence (fun n => (projectiveHilbertFunction (projectiveConeIdeal (L := L) x) n : ℚ)) :=
  projectiveHilbertFunction_eventually_polynomial _ (projectiveConeIdeal_isHomogeneous x)

end DimensionFourDependence
