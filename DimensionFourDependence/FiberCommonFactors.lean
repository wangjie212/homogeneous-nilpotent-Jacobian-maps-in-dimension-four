import DimensionFourDependence.FiberEquationSystem

/-! # Common factors miss the generic point of the fiber

This is the common-factor exclusion used before the degree argument at
the end of Lemma 2.2. It follows from the independent polynomial gradients.
-/

namespace DimensionFourDependence

open MvPolynomial

variable {F A : Type*} [Field F] [Field A] [Algebra F A] {n : ℕ}

/-- The actual polynomial gradient evaluated at a point of a field extension. -/
noncomputable def polynomialGradientAt (x : Fin n → A) (P : MvPolynomial (Fin n) F) : Fin n → A :=
  fun i => aeval x (pderiv i P)

/-- At a zero of one factor, the gradient of a product is a scalar
multiple of that factor's gradient. -/
theorem polynomialGradientAt_mul_of_zero (x : Fin n → A)
    (r P : MvPolynomial (Fin n) F) (hr : aeval x r = 0) :
    polynomialGradientAt x (r * P) = aeval x P • polynomialGradientAt x r := by
  funext i
  simp only [polynomialGradientAt, pderiv_mul, map_add, map_mul, hr, zero_mul,
    add_zero, Pi.smul_apply, smul_eq_mul]
  exact mul_comm _ _

/-- A common factor of two polynomials with independent evaluated
gradients cannot vanish at the evaluation point. -/
theorem common_factor_aeval_ne_zero (x : Fin n → A) (P Q r : MvPolynomial (Fin n) F)
    (hrP : r ∣ P) (hrQ : r ∣ Q)
    (hind : ∀ s t : A, s • polynomialGradientAt x P + t • polynomialGradientAt x Q = 0 →
      s = 0 ∧ t = 0) : aeval x r ≠ 0 := by
  intro hr
  obtain ⟨p, hp⟩ := hrP
  obtain ⟨q, hq⟩ := hrQ
  have hgP : polynomialGradientAt x P = aeval x p • polynomialGradientAt x r := by
    rw [hp]
    exact polynomialGradientAt_mul_of_zero x r p hr
  have hgQ : polynomialGradientAt x Q = aeval x q • polynomialGradientAt x r := by
    rw [hq]
    exact polynomialGradientAt_mul_of_zero x r q hr
  have hrel : aeval x q • polynomialGradientAt x P +
      (-(aeval x p)) • polynomialGradientAt x Q = 0 := by
    rw [hgP, hgQ, smul_smul, smul_smul, ← add_smul]
    have hc : aeval x q * aeval x p + (-(aeval x p)) * aeval x q = 0 := by ring
    rw [hc, zero_smul]
  have hp0 : aeval x p = 0 := neg_eq_zero.mp (hind _ _ hrel).2
  have hon := hind 1 0 (by simp [hgP, hp0])
  exact one_ne_zero hon.1

variable {K : Type*} [Field K] [CharZero K]

/-- The quadratic equation in a fiber witness is nonzero. -/
theorem fiber_witness_quadric_ne_zero
    (H : Fin 4 → FractionRing (MvPolynomial (Fin 4) K)) (W : FiberEquationWitness H) :
    W.quadric ≠ 0 := by
  intro h
  have hon := W.gradients_independent 0 1 (by ext i; simp [h])
  exact one_ne_zero hon.2

/-- The cubic equation in a fiber witness is nonzero. -/
theorem fiber_witness_cubic_ne_zero
    (H : Fin 4 → FractionRing (MvPolynomial (Fin 4) K)) (W : FiberEquationWitness H) :
    W.cubic ≠ 0 := by
  intro h
  have hon := W.gradients_independent 1 0 (by ext i; simp [h])
  exact one_ne_zero hon.1

omit [CharZero K] in
/-- Every common factor of the two constructed fiber equations misses
the actual generic point, as asserted at the end of Lemma 2.2. -/
theorem fiber_witness_common_factor_nonzero
    (H : Fin 4 → FractionRing (MvPolynomial (Fin 4) K)) (W : FiberEquationWitness H)
    (r : MvPolynomial (Fin 3) (coefficientField (K := K) (fun i : Fin 3 => H (W.chart i.castSucc))))
    (hrQ : r ∣ W.quadric) (hrC : r ∣ W.cubic) :
    aeval (fun i => rationalCoordinate (K := K) (W.chart i.castSucc)) r ≠ 0 := by
  apply common_factor_aeval_ne_zero _ W.cubic W.quadric r hrC hrQ
  intro s t hrel
  exact W.gradients_independent s t hrel

end DimensionFourDependence
