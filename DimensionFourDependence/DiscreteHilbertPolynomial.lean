import DimensionFourDependence.HilbertCoordinateRecurrence

/-! # Eventual polynomial sequences and discrete integration

Bernoulli polynomials supply a discrete antiderivative over the rationals.
Thus an eventually polynomial first difference integrates to an eventual
polynomial, without assuming any geometric Hilbert-polynomial theorem.
-/

namespace DimensionFourDependence

open Polynomial

/-- A sequence agrees with the values of a rational polynomial from some index onward. -/
def EventuallyPolynomialSequence (f : ℕ → ℚ) : Prop :=
  ∃ p : Polynomial ℚ, ∃ N : ℕ, ∀ n ≥ N, p.eval (n : ℚ) = f n

/-- A discrete antiderivative, written in the Bernoulli basis. -/
noncomputable def polynomialDiscreteIntegral (p : Polynomial ℚ) : Polynomial ℚ :=
  ∑ k ∈ p.support, (p.coeff k / (k + 1 : ℚ)) • Polynomial.bernoulli (k + 1)

/-- The forward difference of the discrete antiderivative is the original polynomial. -/
theorem polynomialDiscreteIntegral_eval_succ (p : Polynomial ℚ) (x : ℚ) :
    (polynomialDiscreteIntegral p).eval (x + 1) - (polynomialDiscreteIntegral p).eval x = p.eval x := by
  unfold polynomialDiscreteIntegral
  simp only [eval_finsetSum, eval_smul]
  rw [← Finset.sum_sub_distrib]
  calc
    _ = ∑ k ∈ p.support, p.coeff k * x ^ k := by
      apply Finset.sum_congr rfl
      intro k hk
      have hB := Polynomial.bernoulli_eval_one_add (k + 1) x
      rw [add_comm 1 x, Nat.add_sub_cancel] at hB
      rw [hB]
      have hd : (k + 1 : ℚ) ≠ 0 := by positivity
      simp only [smul_eq_mul, Nat.cast_add, Nat.cast_one]
      field_simp
      ring
    _ = p.eval x := by rw [eval_eq_sum, sum_def]

/-- Integrating an eventually polynomial backward difference gives an
eventually polynomial sequence. The integration constant is retained. -/
theorem eventualPolynomial_of_difference (f : ℕ → ℚ) (p : Polynomial ℚ) (N : ℕ)
    (hrec : ∀ n ≥ N, f (n + 1) - f n = p.eval (n + 1 : ℚ)) :
    EventuallyPolynomialSequence f := by
  let D := polynomialDiscreteIntegral p
  let Q := D.comp (X + 1) + C (f N - D.eval (N + 1 : ℚ))
  have hQ (n : ℕ) : Q.eval (n : ℚ) = D.eval (n + 1 : ℚ) + f N - D.eval (N + 1 : ℚ) := by
    simp only [Q, eval_add, eval_comp, eval_X, eval_one, eval_C]
    ring
  have hstep (n : ℕ) : Q.eval (n + 1 : ℚ) - Q.eval (n : ℚ) = p.eval (n + 1 : ℚ) := by
    have he := polynomialDiscreteIntegral_eval_succ p (n + 1 : ℚ)
    have hQ' := hQ (n + 1)
    push_cast at hQ'
    rw [hQ', hQ]
    change _ = _ at he
    dsimp only [D]
    linarith
  refine ⟨Q, N, ?_⟩
  intro n hn
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  induction k with
  | zero => rw [Nat.add_zero, hQ]; ring
  | succ k ih =>
    have hs := hstep (N + k)
    have hr := hrec (N + k) (Nat.le_add_right N k)
    have he : ((N + k : ℕ) : ℚ) + 1 = ((N + k + 1 : ℕ) : ℚ) := by push_cast; rfl
    rw [he] at hs hr
    change Q.eval ((N + k + 1 : ℕ) : ℚ) = f (N + k + 1)
    have hi := ih (Nat.le_add_right N k)
    linarith

/-- A shifted sum of two eventual polynomial sequences is again eventual polynomial. -/
theorem eventualPolynomial_of_shifted_sum (f g h : ℕ → ℚ)
    (hg : EventuallyPolynomialSequence g) (hh : EventuallyPolynomialSequence h)
    (hrec : ∀ n, f (n + 1) = g n + h (n + 1)) : EventuallyPolynomialSequence f := by
  obtain ⟨P, NP, hP⟩ := hg
  obtain ⟨Q, NQ, hQ⟩ := hh
  refine ⟨P.comp (X - 1) + Q, max NP NQ + 1, ?_⟩
  intro n hn
  have hn0 : 1 ≤ n := by omega
  have hpred : n - 1 + 1 = n := Nat.sub_add_cancel hn0
  have hp := hP (n - 1) (by omega)
  have hq := hQ n (by omega)
  have hr := hrec (n - 1)
  rw [hpred] at hr
  simp only [eval_add, eval_comp, eval_sub, eval_X, eval_one]
  have he : (n : ℚ) - 1 = ((n - 1 : ℕ) : ℚ) := by
    simp only [Nat.cast_sub hn0, Nat.cast_one]
  rw [he, hp, hq]
  exact hr.symm

end DimensionFourDependence
