import DimensionFourDependence.NonconstantRatioSpecialization

/-! # A source line preserving a nonconstant rational ratio

The original-field endpoints define an actual polynomial source line.
Its evaluations at zero and one recover the endpoints. Separation of
the two ratio values excludes every constant rational-function value,
so the line-restricted ratio is transcendental over the original field.
-/

namespace DimensionFourDependence

open MvPolynomial

variable {K : Type*} [Field K] {n : ℕ}

/-- The actual source line joining two original-field points. -/
noncomputable def sourcePointLinePolynomial (p q : Fin n → K) : Fin n → Polynomial K :=
  fun i => Polynomial.C (p i) + Polynomial.C (q i - p i) * Polynomial.X

/-- Substitution of the actual line into the original source polynomial. -/
noncomputable def sourceLinePolynomialPullback (p q : Fin n → K)
    (P : MvPolynomial (Fin n) K) : Polynomial K := MvPolynomial.aeval (sourcePointLinePolynomial p q) P

/-- Polynomial line substitution agrees with evaluation at every
actual point on that original-field source line. -/
theorem sourceLinePolynomialPullback_eval (p q : Fin n → K) (P : MvPolynomial (Fin n) K) (z : K) :
    Polynomial.eval z (sourceLinePolynomialPullback p q P) =
      MvPolynomial.eval (fun i => p i + (q i - p i) * z) P := by
  change Polynomial.aeval z (MvPolynomial.aeval (sourcePointLinePolynomial p q) P) =
    MvPolynomial.aeval (fun i => p i + (q i - p i) * z) P
  rw [comp_aeval_apply]
  have he : (fun i => Polynomial.aeval z (sourcePointLinePolynomial p q i)) =
      (fun i => p i + (q i - p i) * z) := by
    funext i
    simp [sourcePointLinePolynomial]
  rw [he]

/-- The source-line polynomial recovers its first actual endpoint. -/
theorem sourceLinePolynomialPullback_eval_zero (p q : Fin n → K) (P : MvPolynomial (Fin n) K) :
    Polynomial.eval 0 (sourceLinePolynomialPullback p q P) = MvPolynomial.eval p P := by
  simpa only [mul_zero, add_zero] using sourceLinePolynomialPullback_eval p q P 0

/-- The source-line polynomial recovers its second actual endpoint. -/
theorem sourceLinePolynomialPullback_eval_one (p q : Fin n → K) (P : MvPolynomial (Fin n) K) :
    Polynomial.eval 1 (sourceLinePolynomialPullback p q P) = MvPolynomial.eval q P := by
  simpa using sourceLinePolynomialPullback_eval p q P 1

/-- A polynomial nonzero at the first endpoint remains a nonzero
actual polynomial after source-line restriction. -/
theorem sourceLinePolynomialPullback_ne_zero (p q : Fin n → K) (P : MvPolynomial (Fin n) K)
    (hp : MvPolynomial.eval p P ≠ 0) : sourceLinePolynomialPullback p q P ≠ 0 := by
  intro hz
  apply hp
  have he : Polynomial.eval 0 (sourceLinePolynomialPullback p q P) = 0 := by rw [hz]; simp
  rwa [sourceLinePolynomialPullback_eval_zero] at he

/-- Different actual ratio values at the two endpoints make the
actual line-restricted rational ratio transcendental over the original field. -/
theorem sourceLine_ratio_transcendental
    (p q : Fin n → K) (f g : MvPolynomial (Fin n) K)
    (hp : MvPolynomial.eval p g ≠ 0)
    (hseparate : MvPolynomial.eval p f * MvPolynomial.eval q g ≠
      MvPolynomial.eval q f * MvPolynomial.eval p g) :
    Transcendental K
      (algebraMap (Polynomial K) (RatFunc K) (sourceLinePolynomialPullback p q f) /
        algebraMap (Polynomial K) (RatFunc K) (sourceLinePolynomialPullback p q g)) := by
  apply RatFunc.transcendental_of_ne_C
  rintro ⟨c, hc⟩
  have hg := sourceLinePolynomialPullback_ne_zero p q g hp
  have hgF : algebraMap (Polynomial K) (RatFunc K) (sourceLinePolynomialPullback p q g) ≠ 0 := by
    intro hz
    apply hg
    apply IsFractionRing.injective (Polynomial K) (RatFunc K)
    simpa only [map_zero] using hz
  have he : sourceLinePolynomialPullback p q f = Polynomial.C c * sourceLinePolynomialPullback p q g := by
    apply IsFractionRing.injective (Polynomial K) (RatFunc K)
    rw [map_mul]
    exact (div_eq_iff hgF).mp hc
  have he0 := congrArg (Polynomial.eval 0) he
  have he1 := congrArg (Polynomial.eval 1) he
  rw [Polynomial.eval_mul, Polynomial.eval_C, sourceLinePolynomialPullback_eval_zero,
    sourceLinePolynomialPullback_eval_zero] at he0
  rw [Polynomial.eval_mul, Polynomial.eval_C, sourceLinePolynomialPullback_eval_one,
    sourceLinePolynomialPullback_eval_one] at he1
  apply hseparate
  rw [he0, he1]
  ring

variable [Infinite K]

/-- A nonconstant original rational polynomial ratio has an actual
original-field source line on which its denominator remains nonzero
and its ratio is transcendental. No general-line assumption is left. -/
theorem exists_source_line_transcendental_ratio
    (f g : MvPolynomial (Fin n) K) (hg : g ≠ 0) (hnot : ¬ ∃ c : K, f = c • g) :
    ∃ p q : Fin n → K, MvPolynomial.eval p g ≠ 0 ∧ MvPolynomial.eval q g ≠ 0 ∧
      sourceLinePolynomialPullback p q g ≠ 0 ∧ Transcendental K
        (algebraMap (Polynomial K) (RatFunc K) (sourceLinePolynomialPullback p q f) /
          algebraMap (Polynomial K) (RatFunc K) (sourceLinePolynomialPullback p q g)) := by
  obtain ⟨p, q, hp, hq, hseparate⟩ :=
    nonproportional_polynomial_ratio_separated_by_source_points f g hg hnot
  exact ⟨p, q, hp, hq, sourceLinePolynomialPullback_ne_zero p q g hp,
    sourceLine_ratio_transcendental p q f g hp hseparate⟩

end DimensionFourDependence
