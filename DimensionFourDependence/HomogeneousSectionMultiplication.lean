import DimensionFourDependence.ProjectiveEmptyHilbertVanishing

/-! # Multiplication by an equation avoiding a finite projective support

When the actual Hilbert function is eventually constant, a homogeneous
equation nonzero everywhere on the support acts invertibly on all
sufficiently large graded quotient pieces. The proof constructs the
quotient multiplication map and derives its surjectivity from the
vanishing Hilbert function of the additional hypersurface section.
-/

namespace DimensionFourDependence

open MvPolynomial Module

attribute [local instance] MvPolynomial.gradedAlgebra

variable {F sigma : Type*} [Field F]

/-- Multiplication by an arbitrary homogeneous polynomial between
the prescribed homogeneous pieces. -/
noncomputable def homogeneousSectionMultiplication
    (S : MvPolynomial sigma F) {d : ℕ} (hS : S.IsHomogeneous d) (n : ℕ) :
    homogeneousSubmodule sigma F n →ₗ[F] homogeneousSubmodule sigma F (n + d) where
  toFun p := ⟨S * (p : MvPolynomial sigma F), by
    change (S * (p : MvPolynomial sigma F)).IsHomogeneous (n + d)
    simpa only [Nat.add_comm] using hS.mul p.property⟩
  map_add' p q := by apply Subtype.ext; simp [mul_add]
  map_smul' a p := by apply Subtype.ext; simp

/-- The actual multiplication map on the homogeneous quotient pieces. -/
noncomputable def homogeneousQuotientSectionMultiplication
    (I : Ideal (MvPolynomial sigma F)) (S : MvPolynomial sigma F)
    {d : ℕ} (hS : S.IsHomogeneous d) (n : ℕ) :
    ((homogeneousSubmodule sigma F n) ⧸ homogeneousRelationSpace I n) →ₗ[F]
      ((homogeneousSubmodule sigma F (n + d)) ⧸ homogeneousRelationSpace I (n + d)) :=
  (homogeneousRelationSpace I n).mapQ (homogeneousRelationSpace I (n + d))
    (homogeneousSectionMultiplication S hS n) (by
      intro p hp
      change S * (p : MvPolynomial sigma F) ∈ I
      exact I.mul_mem_left S hp)

/-- Vanishing of the additional hypersurface's actual quotient piece
makes multiplication onto the corresponding piece of the original quotient. -/
theorem homogeneousQuotientSectionMultiplication_surjective
    [Finite sigma] (I : Ideal (MvPolynomial sigma F))
    (hI : I.IsHomogeneous (homogeneousSubmodule sigma F))
    (S : MvPolynomial sigma F) {d : ℕ} (hS : S.IsHomogeneous d) (n : ℕ)
    (hzero : projectiveHilbertFunction (I ⊔ Ideal.span ({S} : Set (MvPolynomial sigma F))) (n + d) = 0) :
    Function.Surjective (homogeneousQuotientSectionMultiplication I S hS n) := by
  have hrel : homogeneousRelationSpace (I ⊔ Ideal.span ({S} : Set (MvPolynomial sigma F))) (n + d) = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    have he := projectiveHilbertFunction_add_relation_finrank
      (I ⊔ Ideal.span ({S} : Set (MvPolynomial sigma F))) (n + d)
    omega
  intro q
  obtain ⟨r, rfl⟩ := (homogeneousRelationSpace I (n + d)).mkQ_surjective q
  have hr : (r : MvPolynomial sigma F) ∈ I ⊔ Ideal.span ({S} : Set (MvPolynomial sigma F)) := by
    change r ∈ homogeneousRelationSpace (I ⊔ Ideal.span ({S} : Set (MvPolynomial sigma F))) (n + d)
    rw [hrel]
    trivial
  obtain ⟨a, ha, b, hb, he⟩ := Submodule.mem_sup.mp hr
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.mp hb
  change a + b = (r : MvPolynomial sigma F) at he
  rw [hc] at he
  have hv := congrArg (homogeneousComponent (n + d)) he
  rw [map_add, homogeneousComponent_mul_of_isHomogeneous hS c n,
    homogeneousComponent_of_mem r.property, ite_eq_left rfl] at hv
  let c' : homogeneousSubmodule sigma F n :=
    ⟨homogeneousComponent n c, homogeneousComponent_isHomogeneous _ _⟩
  refine ⟨(homogeneousRelationSpace I n).mkQ c', ?_⟩
  apply (Submodule.Quotient.eq (homogeneousRelationSpace I (n + d))).mpr
  change S * homogeneousComponent n c - (r : MvPolynomial sigma F) ∈ I
  have heq : S * homogeneousComponent n c - (r : MvPolynomial sigma F) =
      -homogeneousComponent (n + d) a := by linear_combination hv
  rw [heq]
  exact I.neg_mem (homogeneousComponent_mem_of_mem hI ha _)

/-- Equal dimensions and surjectivity give cancellation of the
homogeneous equation modulo the original ideal in that degree. -/
theorem homogeneous_section_cancel_of_hilbert_dimensions
    [Finite sigma] (I : Ideal (MvPolynomial sigma F))
    (hI : I.IsHomogeneous (homogeneousSubmodule sigma F))
    (S : MvPolynomial sigma F) {d : ℕ} (hS : S.IsHomogeneous d) (n : ℕ)
    (hdim : projectiveHilbertFunction I n = projectiveHilbertFunction I (n + d))
    (hzero : projectiveHilbertFunction (I ⊔ Ideal.span ({S} : Set (MvPolynomial sigma F))) (n + d) = 0)
    (P : MvPolynomial sigma F) (hP : P.IsHomogeneous n) (hSP : S * P ∈ I) : P ∈ I := by
  have hinj : Function.Injective (homogeneousQuotientSectionMultiplication I S hS n) :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mpr
      (homogeneousQuotientSectionMultiplication_surjective I hI S hS n hzero)
  have he : homogeneousQuotientSectionMultiplication I S hS n
      ((homogeneousRelationSpace I n).mkQ ⟨P, hP⟩) = 0 :=
    (Submodule.Quotient.mk_eq_zero _).mpr hSP
  have hq : (homogeneousRelationSpace I n).mkQ ⟨P, hP⟩ = 0 :=
    hinj (he.trans (map_zero _).symm)
  exact (Submodule.Quotient.mk_eq_zero (homogeneousRelationSpace I n)).mp hq

/-- An equation nonzero everywhere on the projective support can be
cancelled in every sufficiently large degree of an eventually constant
actual Hilbert function. -/
theorem homogeneous_section_eventual_cancel_of_support_avoids
    [Finite sigma] (I : Ideal (MvPolynomial sigma F))
    (hI : I.IsHomogeneous (homogeneousSubmodule sigma F))
    (e N : ℕ) (hN : ∀ n ≥ N, projectiveHilbertFunction I n = e)
    (S : MvPolynomial sigma F) {d : ℕ} (hS : S.IsHomogeneous d)
    (havoid : ∀ z : ProjectiveSpectrum (homogeneousSubmodule sigma F),
      I ≤ z.asHomogeneousIdeal.toIdeal → S ∉ z.asHomogeneousIdeal) :
    ∃ M : ℕ, ∀ n ≥ M, ∀ P : MvPolynomial sigma F,
      P.IsHomogeneous n → S * P ∈ I → P ∈ I := by
  have hJ : (I ⊔ Ideal.span ({S} : Set (MvPolynomial sigma F))).IsHomogeneous
      (homogeneousSubmodule sigma F) := by
    apply hI.sup
    apply Ideal.homogeneous_span
    intro P hP
    obtain rfl := Set.mem_singleton_iff.mp hP
    exact ⟨d, hS⟩
  obtain ⟨M, hM⟩ := projectiveHilbertFunction_eventually_zero_of_projective_zeroLocus_empty
    (I ⊔ Ideal.span ({S} : Set (MvPolynomial sigma F))) hJ
    (projective_zeroLocus_add_equation_empty_of_support_avoids I S havoid)
  refine ⟨max N M, ?_⟩
  intro n hn P hP hSP
  exact homogeneous_section_cancel_of_hilbert_dimensions I hI S hS n
    ((hN n (by omega)).trans (hN (n + d) (by omega)).symm)
    (hM (n + d) (by omega)) P hP hSP

end DimensionFourDependence
