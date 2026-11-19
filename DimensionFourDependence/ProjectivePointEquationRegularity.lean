import DimensionFourDependence.TernaryProjectivePointPrincipal
import DimensionFourDependence.ImageRelationNormal

/-! # The equation and generic normal of a ternary direction curve

The entire principal projective relation prime gives irreducibility,
minimal degree, and a nonzero evaluated gradient in characteristic zero.
In particular a homogeneous cofactor not divisible by its equation
cannot vanish at the actual generic direction.
-/

namespace DimensionFourDependence

open MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra

variable {K F σ : Type*} [Field K] [Field F] [Algebra K F]

/-- The entire relation ideal characterizes homogeneous vanishing
by divisibility by its actual original generator. -/
theorem principal_projective_equation_vanishing_iff_dvd
    (A : σ → F) (Φ : MvPolynomial σ K)
    (hI : (projectiveFieldPointIdeal (E := K) A).toIdeal = Ideal.span {Φ})
    (P : MvPolynomial σ K) {e : ℕ} (hP : P.IsHomogeneous e) :
    aeval A P = 0 ↔ Φ ∣ P := by
  rw [← projectiveFieldPointIdeal_mem_homogeneous A P hP, hI, Ideal.mem_span_singleton]

/-- A nonzero homogeneous generator of the relation prime is
irreducible and has positive degree. -/
theorem principal_projective_equation_irreducible_degree_pos
    (A : σ → F) (Φ : MvPolynomial σ K) {d : ℕ}
    (hΦ0 : Φ ≠ 0) (hΦ : Φ.IsHomogeneous d)
    (hI : (projectiveFieldPointIdeal (E := K) A).toIdeal = Ideal.span {Φ}) :
    Irreducible Φ ∧ 0 < d := by
  have hprime : (Ideal.span ({Φ} : Set (MvPolynomial σ K))).IsPrime := by
    rw [← hI]
    exact RingHom.ker_isPrime (projectiveFieldPointMap (E := K) A)
  have hirr := ((Ideal.span_singleton_prime hΦ0).mp hprime).irreducible
  refine ⟨hirr, ?_⟩
  by_contra hn
  have hd : d = 0 := by omega
  exact hirr.not_isUnit (isUnit_of_isHomogeneous_zero (hd ▸ hΦ) hΦ0)

/-- The gradient of the actual generator does not vanish at the
generic point. Any nonzero derivative has strictly smaller degree,
and so cannot be another member of the principal relation ideal. -/
theorem principal_projective_equation_gradient_ne_zero [CharZero K] [Fintype σ]
    (A : σ → F) (Φ : MvPolynomial σ K) {d : ℕ}
    (hΦ0 : Φ ≠ 0) (hΦ : Φ.IsHomogeneous d)
    (hI : (projectiveFieldPointIdeal (E := K) A).toIdeal = Ideal.span {Φ}) :
    (fun i => aeval A (pderiv i Φ)) ≠ 0 := by
  have hd := (principal_projective_equation_irreducible_degree_pos A Φ hΦ0 hΦ hI).2
  intro hz
  apply hΦ0
  apply eq_zero_of_forall_pderiv_eq_zero hΦ (by omega)
  intro i
  by_contra hi
  have hdvd := (principal_projective_equation_vanishing_iff_dvd A Φ hI
    (pderiv i Φ) hΦ.pderiv).mp (congrFun hz i)
  have hle := totalDegree_le_of_dvd_of_isDomain hdvd hi
  rw [hΦ.totalDegree hΦ0] at hle
  have hsmall := (hΦ.pderiv (i := i)).totalDegree_le
  omega

/-- The generic direction belongs to its own tangent line, by Euler's
identity for the actual homogeneous defining equation. -/
theorem homogeneous_equation_gradient_annihilates_point [Fintype σ]
    (A : σ → F) (Φ : MvPolynomial σ K) {d : ℕ}
    (hΦ : Φ.IsHomogeneous d) (hzero : aeval A Φ = 0) :
    ∑ i, A i * aeval A (pderiv i Φ) = 0 := by
  classical
  have he := congrArg (aeval A) hΦ.sum_X_mul_pderiv
  simpa only [map_sum, map_mul, aeval_X, map_nsmul, hzero, nsmul_zero] using he

/-- A nonconstant ternary direction constrained by an original proper
homogeneous equation constructs its entire irreducible curve equation,
its nonzero generic gradient, and the exact homogeneous divisibility test. -/
theorem nonconstant_ternary_direction_constructs_regular_equation [CharZero K]
    (A : Fin 3 → F) (j : Fin 3) (hj : A j ≠ 0)
    (hdim : Algebra.trdeg K (projectiveRatioField (K := K) A j) ≠ 0)
    (Q : MvPolynomial (Fin 3) K) {e : ℕ} (hQ0 : Q ≠ 0)
    (hQ : Q.IsHomogeneous e) (hzero : aeval A Q = 0) :
    ∃ (Φ : MvPolynomial (Fin 3) K) (d : ℕ),
      Φ ≠ 0 ∧ Φ.IsHomogeneous d ∧ 0 < d ∧ Irreducible Φ ∧ aeval A Φ = 0 ∧
      (projectiveFieldPointIdeal (E := K) A).toIdeal = Ideal.span {Φ} ∧
      (fun i => aeval A (pderiv i Φ)) ≠ 0 ∧
      ∀ (P : MvPolynomial (Fin 3) K) (f : ℕ),
        P.IsHomogeneous f → (aeval A P = 0 ↔ Φ ∣ P) := by
  obtain ⟨Φ, d, hΦ, hI⟩ :=
    nonconstant_ternary_projective_point_exists_homogeneous_generator A j hj hdim
  have hΦ0 : Φ ≠ 0 := by
    intro hz
    have hmem := (projectiveFieldPointIdeal_mem_homogeneous A Q hQ).mpr hzero
    rw [hI, hz, Ideal.span_singleton_zero, Ideal.mem_bot] at hmem
    exact hQ0 hmem
  obtain ⟨hirr, hd⟩ := principal_projective_equation_irreducible_degree_pos A Φ hΦ0 hΦ hI
  have hvalue : aeval A Φ = 0 :=
    (principal_projective_equation_vanishing_iff_dvd A Φ hI Φ hΦ).mpr (dvd_refl Φ)
  refine ⟨Φ, d, hΦ0, hΦ, hd, hirr, hvalue, hI,
    principal_projective_equation_gradient_ne_zero A Φ hΦ0 hΦ hI, ?_⟩
  intro P f hP
  exact principal_projective_equation_vanishing_iff_dvd A Φ hI P hP

end DimensionFourDependence
