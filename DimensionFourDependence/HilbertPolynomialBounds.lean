import DimensionFourDependence.HilbertPolynomialExistence

/-! # The actual Hilbert polynomial and its linear growth bound

The polynomial is chosen from the proved existence theorem and is unique.
An eventual nonnegative linear bound rules out every higher degree.
-/

namespace DimensionFourDependence

open Module Polynomial Filter

variable {L σ : Type*} [Field L] [Finite σ]

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The Hilbert polynomial of the actual homogeneous quotient. -/
noncomputable def projectiveHilbertPolynomial (I : Ideal (MvPolynomial σ L))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ L)) : Polynomial ℚ :=
  Classical.choose (projectiveHilbertFunction_eventually_polynomial I hI)

theorem projectiveHilbertPolynomial_spec (I : Ideal (MvPolynomial σ L))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ L)) :
    ∃ N : ℕ, ∀ n ≥ N, (projectiveHilbertPolynomial I hI).eval (n : ℚ) = projectiveHilbertFunction I n :=
  Classical.choose_spec (projectiveHilbertFunction_eventually_polynomial I hI)

/-- Agreement on all sufficiently large natural arguments determines the polynomial. -/
theorem polynomial_eq_of_eventual_nat_eval_eq (p q : Polynomial ℚ) (N : ℕ)
    (h : ∀ n ≥ N, p.eval (n : ℚ) = q.eval (n : ℚ)) : p = q := by
  apply p.eq_of_infinite_eval_eq q
  have hi : Function.Injective (fun n : ℕ => ((n + N : ℕ) : ℚ)) := by
    intro a b hab
    exact Nat.add_right_cancel (Nat.cast_inj.mp hab)
  apply (Set.infinite_range_of_injective hi).mono
  rintro _ ⟨n, rfl⟩
  exact h (n + N) (Nat.le_add_left N n)

theorem projectiveHilbertPolynomial_unique (I : Ideal (MvPolynomial σ L))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ L)) (p : Polynomial ℚ) (N : ℕ)
    (hp : ∀ n ≥ N, p.eval (n : ℚ) = projectiveHilbertFunction I n) :
    p = projectiveHilbertPolynomial I hI := by
  obtain ⟨M, hM⟩ := projectiveHilbertPolynomial_spec I hI
  apply polynomial_eq_of_eventual_nat_eval_eq p _ (max N M)
  intro n hn
  rw [hp n (by omega), hM n (by omega)]

/-- A polynomial with nonnegative values bounded linearly at large natural
arguments has degree at most one. -/
theorem polynomial_natDegree_le_one_of_nat_linear_bound (p : Polynomial ℚ) (A : ℚ) (N : ℕ)
    (hb : ∀ n ≥ N, 0 ≤ p.eval (n : ℚ) ∧ p.eval (n : ℚ) ≤ A * (n + 1)) : p.natDegree ≤ 1 := by
  by_contra h
  have hd : 1 < p.natDegree := lt_of_not_ge h
  have hdeg : 0 < p.degree := Polynomial.natDegree_pos_iff_degree_pos.mp (by omega)
  have hlc : 0 ≤ p.leadingCoeff := by
    by_contra hneg
    have ht := (p.tendsto_atBot_of_leadingCoeff_nonpos hdeg (le_of_lt (lt_of_not_ge hneg))).comp
      (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℚ)) atTop atTop)
    obtain ⟨n, hn0, hn⟩ := ((ht.eventually_lt_atBot 0).and (eventually_ge_atTop N)).exists
    exact not_lt_of_ge (hb n hn).1 hn0
  have hlcpos : 0 < p.leadingCoeff :=
    lt_of_le_of_ne hlc (Ne.symm (leadingCoeff_ne_zero.mpr (ne_zero_of_degree_gt hdeg)))
  let B : Polynomial ℚ := C A * (X + 1)
  have hB : B.natDegree ≤ 1 := by
    apply (natDegree_C_mul_le A (X + 1)).trans
    simpa only [← C_1] using (natDegree_X_add_C (1 : ℚ)).le
  have hsmall : B.degree < p.degree := degree_lt_degree (hB.trans_lt hd)
  let Q := p - B
  have hQdeg : 0 < Q.degree := by
    dsimp only [Q]
    rw [degree_sub_eq_left_of_degree_lt hsmall]
    exact hdeg
  have hQlc : 0 ≤ Q.leadingCoeff := by
    dsimp only [Q]
    rw [leadingCoeff_sub_of_degree_lt hsmall]
    exact hlcpos.le
  have ht := (Q.tendsto_atTop_of_leadingCoeff_nonneg hQdeg hQlc).comp
    (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℚ)) atTop atTop)
  obtain ⟨n, hn0, hn⟩ := ((ht.eventually_gt_atTop 0).and (eventually_ge_atTop N)).exists
  have hv := (hb n hn).2
  dsimp only [Q, B] at hn0
  simp only [eval_sub, eval_mul, eval_C, eval_add, eval_X, eval_one] at hn0
  change 0 < p.eval (n : ℚ) - A * ((n : ℚ) + 1) at hn0
  linarith

/-- In a linear polynomial with eventually nonnegative values bounded
by `A(n+1)`, its slope lies between zero and `A`. -/
theorem polynomial_slope_bounds (p : Polynomial ℚ) (hp : p.natDegree ≤ 1) (A : ℚ) (N : ℕ)
    (hb : ∀ n ≥ N, 0 ≤ p.eval (n : ℚ) ∧ p.eval (n : ℚ) ≤ A * (n + 1)) :
    0 ≤ p.coeff 1 ∧ p.coeff 1 ≤ A := by
  have he (n : ℕ) : p.eval (n : ℚ) = p.coeff 1 * n + p.coeff 0 := by
    conv_lhs => rw [eq_X_add_C_of_natDegree_le_one hp]
    simp
  constructor
  · by_contra h
    have hneg : p.coeff 1 < 0 := lt_of_not_ge h
    obtain ⟨n, hn⟩ := exists_nat_gt (p.coeff 0 / (-p.coeff 1))
    have hm : p.coeff 0 / (-p.coeff 1) < ((max N n : ℕ) : ℚ) :=
      hn.trans_le (by exact_mod_cast le_max_right N n)
    have hprod := (div_lt_iff₀ (neg_pos.mpr hneg)).mp hm
    have hv := (hb (max N n) (le_max_left N n)).1
    rw [he] at hv
    nlinarith
  · by_contra h
    have hpos : 0 < p.coeff 1 - A := sub_pos.mpr (lt_of_not_ge h)
    obtain ⟨n, hn⟩ := exists_nat_gt ((A - p.coeff 0) / (p.coeff 1 - A))
    have hm : (A - p.coeff 0) / (p.coeff 1 - A) < ((max N n : ℕ) : ℚ) :=
      hn.trans_le (by exact_mod_cast le_max_right N n)
    have hprod := (div_lt_iff₀ hpos).mp hm
    have hv := (hb (max N n) (le_max_left N n)).2
    rw [he] at hv
    nlinarith

end DimensionFourDependence
