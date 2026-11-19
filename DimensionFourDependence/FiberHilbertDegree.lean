import DimensionFourDependence.FiberHilbertLowerBound

/-! # The generic fiber's positive integral Hilbert degree is at most six

The degree is characterized by the coefficient of `n` in the actual eventual
Hilbert polynomial. The result here is over the actual coefficient field;
passage to geometric generic components is a separate base-change step.
-/

namespace DimensionFourDependence

open Polynomial

/-- An eventual linear polynomial taking natural-number values has an
integral intercept and a natural slope when that slope is nonnegative. -/
theorem polynomial_integer_linear_data (f : ℕ → ℕ) (p : Polynomial ℚ)
    (hp : p.natDegree ≤ 1) (hs : 0 ≤ p.coeff 1) (N : ℕ)
    (heval : ∀ n ≥ N, p.eval (n : ℚ) = f n) :
    ∃ e : ℕ, ∃ b : ℤ, (e : ℚ) = p.coeff 1 ∧ (b : ℚ) = p.coeff 0 ∧
      ∀ n ≥ N, (f n : ℤ) = (e : ℤ) * n + b := by
  have he (n : ℕ) : p.eval (n : ℚ) = p.coeff 1 * n + p.coeff 0 := by
    conv_lhs => rw [eq_X_add_C_of_natDegree_le_one hp]
    simp
  have h0 := heval N le_rfl
  have h1 := heval (N + 1) (by omega)
  rw [he] at h0 h1
  push_cast at h0 h1
  have hle : f N ≤ f (N + 1) := by
    have hq : (f N : ℚ) ≤ f (N + 1) := by linarith
    exact_mod_cast hq
  let e := f (N + 1) - f N
  have he' : (e : ℚ) = p.coeff 1 := by
    dsimp only [e]
    rw [Nat.cast_sub hle]
    linarith
  let b : ℤ := (f N : ℤ) - (e : ℤ) * N
  have hb : (b : ℚ) = p.coeff 0 := by
    dsimp only [b]
    push_cast
    rw [he']
    linarith
  refine ⟨e, b, he', hb, ?_⟩
  intro n hn
  have hv := heval n hn
  rw [he] at hv
  have hq : (f n : ℚ) = (e : ℚ) * n + (b : ℚ) := by rw [he', hb]; linarith
  exact_mod_cast hq

variable {L σ : Type*} [Field L]

/-- A positive Hilbert degree is the leading coefficient of an eventual
linear Hilbert polynomial, expressed with its integral constant term. -/
def HasCurveHilbertDegree (I : Ideal (MvPolynomial σ L)) (e : ℕ) : Prop :=
  0 < e ∧ ∃ b : ℤ, ∃ N : ℕ, ∀ n ≥ N,
    (projectiveHilbertFunction I n : ℤ) = (e : ℤ) * n + b

/-- The degree characterized by the eventual Hilbert function is unique. -/
theorem curveHilbertDegree_unique (I : Ideal (MvPolynomial σ L)) {e e' : ℕ}
    (he : HasCurveHilbertDegree I e) (he' : HasCurveHilbertDegree I e') : e = e' := by
  obtain ⟨_, b, N, hN⟩ := he
  obtain ⟨_, b', M, hM⟩ := he'
  have h0 := (hN (max N M) (le_max_left N M)).symm.trans (hM _ (le_max_right N M))
  have h1 := (hN (max N M + 1) (by omega)).symm.trans (hM _ (by omega))
  push_cast at h0 h1
  have heq : (e : ℤ) = e' := by nlinarith
  exact_mod_cast heq

attribute [local instance] MvPolynomial.gradedAlgebra

/-- A homogeneous quotient whose Hilbert function lies between `n+1`
and `6(n+1)` has a positive integral Hilbert degree at most six. -/
theorem exists_curve_hilbert_degree_of_linear_bounds [Finite σ]
    (I : Ideal (MvPolynomial σ L)) (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ L))
    (hlower : ∀ n, n + 1 ≤ projectiveHilbertFunction I n)
    (hupper : ∀ n ≥ 5, projectiveHilbertFunction I n ≤ 6 * (n + 1)) :
    ∃ e : ℕ, e ≤ 6 ∧ HasCurveHilbertDegree I e := by
  let p := projectiveHilbertPolynomial I hI
  obtain ⟨N, hP⟩ := projectiveHilbertPolynomial_spec I hI
  have hb (n : ℕ) (hn : max N 5 ≤ n) :
      0 ≤ p.eval (n : ℚ) ∧ p.eval (n : ℚ) ≤ 6 * (n + 1) := by
    change 0 ≤ (projectiveHilbertPolynomial I hI).eval (n : ℚ) ∧ _
    rw [hP n (by omega)]
    constructor
    · positivity
    · exact_mod_cast hupper n (by omega)
  have hp := polynomial_natDegree_le_one_of_nat_linear_bound p 6 (max N 5) hb
  have hs := polynomial_slope_bounds p hp 6 (max N 5) hb
  let q : Polynomial ℚ := p - (X + 1)
  have hq : q.natDegree ≤ 1 := by
    apply (natDegree_sub_le p (X + 1)).trans
    apply max_le hp
    simpa only [← C_1] using (natDegree_X_add_C (1 : ℚ)).le
  have hbq (n : ℕ) (hn : max N 5 ≤ n) :
      0 ≤ q.eval (n : ℚ) ∧ q.eval (n : ℚ) ≤ 6 * (n + 1) := by
    have hlo : (n : ℚ) + 1 ≤ p.eval (n : ℚ) := by
      change (n : ℚ) + 1 ≤ (projectiveHilbertPolynomial I hI).eval (n : ℚ)
      rw [hP n (by omega)]
      exact_mod_cast hlower n
    have hup := (hb n hn).2
    dsimp only [q]
    simp only [eval_sub, eval_add, eval_X, eval_one]
    constructor <;> nlinarith [show (0 : ℚ) ≤ n by positivity]
  have hs1 : 1 ≤ p.coeff 1 := by
    have h := (polynomial_slope_bounds q hq 6 (max N 5) hbq).1
    dsimp only [q] at h
    norm_num [Polynomial.coeff_one] at h
    linarith
  obtain ⟨e, b, he, _, hlin⟩ := polynomial_integer_linear_data
    (projectiveHilbertFunction I) p hp hs.1 N hP
  have he6 : e ≤ 6 := by
    have h : (e : ℚ) ≤ 6 := by rw [he]; exact hs.2
    exact_mod_cast h
  have hepos : 0 < e := by
    have h : (1 : ℚ) ≤ e := by rw [he]; exact hs1
    have hnat : 1 ≤ e := by exact_mod_cast h
    omega
  exact ⟨e, he6, hepos, b, N, hlin⟩

variable {K : Type*} [Field K] [CharZero K]

/-- The actual generic fiber closure has positive integral Hilbert
degree at most six, under the original nilpotent rank-three hypotheses. -/
theorem projective_fiber_witness_curve_hilbert_degree
    (H : Fin 4 → FractionRing (MvPolynomial (Fin 4) K))
    (hN : IsNilpotent (rationalJacobian H)) (hrank : (rationalJacobian H).rank = 3)
    (W : ProjectiveFiberEquationWitness H) :
    ∃ e : ℕ, e ≤ 6 ∧ HasCurveHilbertDegree (projectiveConeIdeal
      (L := coefficientField (K := K) (fun i : Fin 3 => H (W.affine.chart i.castSucc)))
      (fun i : Fin 3 => rationalCoordinate (K := K) (W.affine.chart i.castSucc))) e := by
  apply exists_curve_hilbert_degree_of_linear_bounds _ (projectiveConeIdeal_isHomogeneous _)
  · exact projective_fiber_witness_hilbert_lower_bound H hN hrank W
  · exact projective_fiber_witness_hilbert_le_six H W

end DimensionFourDependence
