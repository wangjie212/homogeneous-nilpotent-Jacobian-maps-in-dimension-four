import DimensionFourDependence.FiberHilbertDegree

/-! # The curve degree is the eventual Hilbert dimension of a hyperplane section

For a homogeneous prime and a coordinate outside it, the colon ideal
is unchanged. The actual graded-coordinate recurrence then identifies
the hyperplane section's eventual Hilbert function with the curve's
Hilbert degree. This includes the original projective closure and its
actual infinity hyperplane, whose coordinate is proved not to vanish
identically. A section-dimension bound therefore gives the degree bound.
-/

namespace DimensionFourDependence

open MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra

variable {L sigma : Type*} [Field L]

/-- A coordinate outside the prime is a nonzero divisor in the quotient,
so the actual coordinate colon ideal equals the original prime. -/
theorem coordinateColon_eq_of_prime
    (I : Ideal (MvPolynomial sigma L)) [I.IsPrime] (i : sigma) (hi : X i ∉ I) :
    coordinateColon I i = I := by
  apply le_antisymm
  · intro p hp
    have hm : X i * p ∈ I := by
      simpa only [smul_eq_mul, mul_comm] using Submodule.mem_colon_singleton.mp hp
    exact (‹I.IsPrime›.mem_or_mem hm).resolve_left hi
  · exact le_coordinateColon I i

/-- The actual homogeneous hyperplane-section quotient has eventual
Hilbert function equal to the curve's already defined Hilbert degree. -/
theorem hyperplane_section_eventual_hilbert_dimension
    [Finite sigma] (I : Ideal (MvPolynomial sigma L)) [I.IsPrime]
    (hI : I.IsHomogeneous (homogeneousSubmodule sigma L))
    (i : sigma) (hi : X i ∉ I) {e : ℕ} (he : HasCurveHilbertDegree I e) :
    ∃ N : ℕ, ∀ n ≥ N,
      projectiveHilbertFunction (I ⊔ Ideal.span ({X i} : Set (MvPolynomial sigma L))) (n + 1) = e := by
  obtain ⟨_hepos, b, N, hN⟩ := he
  refine ⟨N, ?_⟩
  intro n hn
  have h0 := hN n hn
  have h1 := hN (n + 1) (by omega)
  have hr := projectiveHilbertFunction_coordinate_recurrence I hI i n
  rw [coordinateColon_eq_of_prime I i hi] at hr
  have hr' : (projectiveHilbertFunction I (n + 1) : ℤ) =
      (projectiveHilbertFunction I n : ℤ) +
        (projectiveHilbertFunction (I ⊔ Ideal.span ({X i} : Set (MvPolynomial sigma L))) (n + 1) : ℤ) := by
    exact_mod_cast hr
  have hsec : (projectiveHilbertFunction (I ⊔ Ideal.span ({X i} : Set (MvPolynomial sigma L))) (n + 1) : ℤ) = e := by
    push_cast at h1
    nlinarith
  exact_mod_cast hsec

/-- An eventual bound on the actual hyperplane-section quotient bounds
the actual curve degree; no geometric degree comparison is assumed. -/
theorem curve_hilbert_degree_le_of_hyperplane_section_bound
    [Finite sigma] (I : Ideal (MvPolynomial sigma L)) [I.IsPrime]
    (hI : I.IsHomogeneous (homogeneousSubmodule sigma L))
    (i : sigma) (hi : X i ∉ I) {e m : ℕ} (he : HasCurveHilbertDegree I e)
    (M : ℕ) (hbound : ∀ n ≥ M,
      projectiveHilbertFunction (I ⊔ Ideal.span ({X i} : Set (MvPolynomial sigma L))) n ≤ m) : e ≤ m := by
  obtain ⟨N, hN⟩ := hyperplane_section_eventual_hilbert_dimension I hI i hi he
  have hv := hN (max N M) (le_max_left N M)
  rw [← hv]
  exact hbound _ (by omega)

variable {F : Type*} [Field F] [Algebra L F]

/-- For the actual projective closure the actual infinity-section
Hilbert function equals the curve degree in all sufficiently large degrees. -/
theorem projective_closure_infinity_eventual_hilbert_dimension
    [Finite sigma] (x : sigma → F) {e : ℕ}
    (he : HasCurveHilbertDegree (projectiveConeIdeal (L := L) x) e) :
    ∃ N : ℕ, ∀ n ≥ N,
      projectiveHilbertFunction (projectiveConeIdeal (L := L) x ⊔
        Ideal.span ({X none} : Set (MvPolynomial (Option sigma) L))) (n + 1) = e :=
  hyperplane_section_eventual_hilbert_dimension (projectiveConeIdeal (L := L) x)
    (projectiveConeIdeal_isHomogeneous (L := L) x) none
    (projectiveConeIdeal_X_none_not_mem (L := L) x) he

/-- The original projective closure has degree at most two once its
actual infinity-section Hilbert dimensions are at most two. -/
theorem projective_closure_degree_le_two_of_infinity_section_bound
    [Finite sigma] (x : sigma → F) {e : ℕ}
    (he : HasCurveHilbertDegree (projectiveConeIdeal (L := L) x) e)
    (M : ℕ) (hbound : ∀ n ≥ M,
      projectiveHilbertFunction (projectiveConeIdeal (L := L) x ⊔
        Ideal.span ({X none} : Set (MvPolynomial (Option sigma) L))) n ≤ 2) : e ≤ 2 :=
  curve_hilbert_degree_le_of_hyperplane_section_bound (projectiveConeIdeal (L := L) x)
    (projectiveConeIdeal_isHomogeneous (L := L) x) none
    (projectiveConeIdeal_X_none_not_mem (L := L) x) he M hbound

end DimensionFourDependence
