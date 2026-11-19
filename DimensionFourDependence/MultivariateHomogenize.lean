import DimensionFourDependence.FiberPolynomialForms

/-! # Homogenizing multivariate fiber equations to their actual degrees

The new variable is indexed by `none`; the affine variables are indexed
by `some`. This is independent of any choice of projective coordinate order.
-/

namespace DimensionFourDependence

open MvPolynomial

variable {R σ τ : Type*} [Field R]

/-- Substituting affine-linear polynomials does not increase total degree. -/
theorem totalDegree_aeval_le_of_linear (v : σ → MvPolynomial τ R)
    (hv : ∀ i, (v i).totalDegree ≤ 1) (p : MvPolynomial σ R) :
    (aeval v p).totalDegree ≤ p.totalDegree := by
  classical
  have hpow (i : σ) (k : ℕ) : ((v i) ^ k).totalDegree ≤ k := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ]
      exact (totalDegree_mul _ _).trans (Nat.add_le_add ih (hv i))
  have hs : aeval v p = ∑ m ∈ p.support, aeval v (monomial m (p.coeff m)) := by
    rw [← map_sum, ← p.as_sum]
  rw [hs]
  apply totalDegree_finsetSum_le
  intro m hm
  rw [aeval_monomial]
  have hprod : (m.prod (fun i k => v i ^ k)).totalDegree ≤ m.degree := by
    change (∏ i ∈ m.support, v i ^ m i).totalDegree ≤ ∑ i ∈ m.support, m i
    exact (totalDegree_finsetProd _ _).trans (Finset.sum_le_sum fun i _ => hpow i (m i))
  have hmdeg : m.degree ≤ p.totalDegree := by
    simpa only [Finsupp.degree_apply, Finsupp.sum] using le_totalDegree hm
  have hmul := totalDegree_mul (C (p.coeff m)) (m.prod (fun i k => v i ^ k))
  simp only [totalDegree_C, zero_add] at hmul
  exact hmul.trans (hprod.trans hmdeg)

/-- The affine chart obtained by setting the homogenizing variable to one. -/
noncomputable def projectiveDehomogenize : MvPolynomial (Option σ) R →ₐ[R] MvPolynomial σ R :=
  aeval (fun j : Option σ => j.elim 1 X)

theorem projectiveDehomogenize_X_none :
    projectiveDehomogenize (X (none : Option σ) : MvPolynomial (Option σ) R) = 1 := by
  simp [projectiveDehomogenize]

theorem projectiveDehomogenize_X_some (i : σ) :
    projectiveDehomogenize (X (some i) : MvPolynomial (Option σ) R) = X i := by
  simp [projectiveDehomogenize]

theorem projectiveDehomogenize_rename (p : MvPolynomial σ R) :
    projectiveDehomogenize (rename some p) = p := by
  have he : (projectiveDehomogenize (R := R) (σ := σ)).comp (rename some) = AlgHom.id R _ := by
    apply MvPolynomial.algHom_ext
    intro i
    simp [projectiveDehomogenize]
  exact DFunLike.congr_fun he p

theorem projectiveDehomogenize_totalDegree (p : MvPolynomial (Option σ) R) :
    (projectiveDehomogenize p).totalDegree ≤ p.totalDegree := by
  change (aeval (fun j : Option σ => j.elim 1 X) p).totalDegree ≤ p.totalDegree
  apply totalDegree_aeval_le_of_linear
  intro i
  cases i <;> simp

/-- Homogenize each monomial by adding the missing power of the new variable. -/
noncomputable def projectiveHomogenize (p : MvPolynomial σ R) (d : ℕ) : MvPolynomial (Option σ) R := by
  classical
  exact ∑ m ∈ p.support, rename some (monomial m (p.coeff m)) * X none ^ (d - m.degree)

theorem projectiveHomogenize_zero (d : ℕ) :
    projectiveHomogenize (0 : MvPolynomial σ R) d = 0 := by
  simp [projectiveHomogenize]

/-- Dehomogenization recovers the original polynomial, even if the
requested degree was smaller than its total degree. -/
theorem projectiveDehomogenize_homogenize (p : MvPolynomial σ R) (d : ℕ) :
    projectiveDehomogenize (projectiveHomogenize p d) = p := by
  classical
  unfold projectiveHomogenize
  rw [map_sum]
  simp only [map_mul, projectiveDehomogenize_rename, map_pow,
    projectiveDehomogenize_X_none, one_pow, mul_one]
  exact support_sum_monomial_coeff p

theorem projectiveHomogenize_injective (d : ℕ) :
    Function.Injective (fun p : MvPolynomial σ R => projectiveHomogenize p d) := by
  intro p q h
  have he := congrArg (projectiveDehomogenize (R := R) (σ := σ)) h
  simpa only [projectiveDehomogenize_homogenize] using he

theorem projectiveHomogenize_ne_zero {p : MvPolynomial σ R} (hp : p ≠ 0) (d : ℕ) :
    projectiveHomogenize p d ≠ 0 := by
  intro h
  apply hp
  have he := congrArg (projectiveDehomogenize (R := R) (σ := σ)) h
  simpa only [projectiveDehomogenize_homogenize, map_zero] using he

/-- Every term has the prescribed degree when it bounds the affine degree. -/
theorem projectiveHomogenize_isHomogeneous (p : MvPolynomial σ R) (d : ℕ)
    (hd : p.totalDegree ≤ d) : (projectiveHomogenize p d).IsHomogeneous d := by
  classical
  unfold projectiveHomogenize
  apply IsHomogeneous.sum
  intro m hm
  have hmdeg : m.degree ≤ d := by
    have h := (le_totalDegree hm).trans hd
    simpa only [Finsupp.degree_apply, Finsupp.sum] using h
  have hmono : (rename some (monomial m (p.coeff m))).IsHomogeneous m.degree :=
    (isHomogeneous_monomial (p.coeff m) rfl).rename_isHomogeneous
  have h := hmono.mul (isHomogeneous_X_pow (none : Option σ) (d - m.degree))
  have he : m.degree + (d - m.degree) = d := by omega
  simpa only [he] using h

theorem projectiveHomogenize_totalDegree {p : MvPolynomial σ R} (hp : p ≠ 0)
    (d : ℕ) (hd : p.totalDegree ≤ d) : (projectiveHomogenize p d).totalDegree = d :=
  (projectiveHomogenize_isHomogeneous p d hd).totalDegree (projectiveHomogenize_ne_zero hp d)

/-- Homogenizing to the actual degree introduces no extra factor at infinity. -/
theorem X_none_not_dvd_projectiveHomogenize {p : MvPolynomial σ R} (hp : p ≠ 0) :
    ¬ (X (none : Option σ) : MvPolynomial (Option σ) R) ∣ projectiveHomogenize p p.totalDegree := by
  intro hdiv
  obtain ⟨q, hq⟩ := hdiv
  have hH := projectiveHomogenize_ne_zero hp p.totalDegree
  have hq0 : q ≠ 0 := by
    intro h
    exact hH (by rw [hq, h, mul_zero])
  have hdeg := projectiveHomogenize_totalDegree hp p.totalDegree le_rfl
  rw [hq, totalDegree_mul_of_isDomain (X_ne_zero (none : Option σ)) hq0, totalDegree_X] at hdeg
  have hdeq : projectiveDehomogenize q = p := by
    have h := congrArg (projectiveDehomogenize (R := R) (σ := σ)) hq
    simpa only [projectiveDehomogenize_homogenize, map_mul, projectiveDehomogenize_X_none,
      one_mul] using h.symm
  have hb := projectiveDehomogenize_totalDegree q
  rw [hdeq] at hb
  omega

end DimensionFourDependence
