import DimensionFourDependence.UnivariateLinearPowerDescent

/-! # Descent of a scalar times an affine linear power -/

namespace DimensionFourDependence

open MvPolynomial

set_option maxHeartbeats 3000000

variable {K E : Type*} [Field K] [Field E] [CharZero E]

/-- Homogenization of a pure affine power retains its original constant
and linear coefficients, including a constant affine form. -/
theorem affine_linear_power_homogenize (a : Fin 2 → E) (d : ℕ) :
    (segreRulingAffineFactor a ^ d).homogenize d = linearFormPolynomial ![a 1, a 0] ^ d := by
  apply Polynomial.homogenize_eq_of_isHomogeneous
  · simpa only [Nat.one_mul] using (linearFormPolynomial_homogeneous ![a 1, a 0]).pow d
  · have ha : ![a 0, a 1] = a := by funext i; fin_cases i <;> rfl
    simp only [map_pow, binary_linear_form_dehomogenize,
      Matrix.cons_val_zero, Matrix.cons_val_one, ha]

/-- An original polynomial which becomes a scalar times a pure affine
linear power has the same kind of factorization over its original field.
The scalar and linear polynomial are constructed by coefficient descent. -/
theorem univariate_scalar_linear_power_factorization_descends
    (f : K →+* E) (P : Polynomial K) (hP : P ≠ 0)
    (a : Fin 2 → E) (α : E) (hα : α ≠ 0) (d : ℕ) (hd : 0 < d)
    (hfactor : P.map f = Polynomial.C α * segreRulingAffineFactor a ^ d) :
    ∃ (β : K) (B : Polynomial K), β ≠ 0 ∧ B ≠ 0 ∧ B.natDegree ≤ 1 ∧
      P = Polynomial.C β * B ^ d := by
  have hdegree : P.natDegree ≤ d := by
    rw [← Polynomial.natDegree_map f, hfactor]
    exact Polynomial.natDegree_mul_le.trans (by
      simp only [Polynomial.natDegree_C, Nat.zero_add]
      exact Polynomial.natDegree_pow_le.trans (by
        simpa only [Nat.mul_one] using
          Nat.mul_le_mul_left d (segreRulingAffineFactor_natDegree_le_one a)))
  have hhom : MvPolynomial.map f (P.homogenize d) =
      MvPolynomial.C α * linearFormPolynomial ![a 1, a 0] ^ d := by
    rw [← Polynomial.homogenize_map, hfactor,
      Polynomial.homogenize_C_mul, affine_linear_power_homogenize]
  have ha : ![a 1, a 0] ≠ (0 : Fin 2 → E) := by
    intro hz
    apply hP
    apply Polynomial.map_injective f f.injective
    rw [hfactor, Polynomial.map_zero]
    have h0 := congrFun hz 1
    have h1 := congrFun hz 0
    change a 0 = 0 at h0
    change a 1 = 0 at h1
    simp [segreRulingAffineFactor, h0, h1, hd.ne']
  obtain ⟨j, hj⟩ : ∃ j, (![a 1, a 0] : Fin 2 → E) j ≠ 0 := by
    simpa only [ne_eq, funext_iff, Pi.zero_apply, not_forall] using ha
  obtain ⟨b, _hbj, _hb, hβ, he⟩ := linear_power_factorization_descends f (P.homogenize d)
    hd ![a 1, a 0] α hα j hj hhom
  let β := MvPolynomial.eval (Pi.single j 1) (P.homogenize d)
  let B := segreRulingAffineFactor ![b 1, b 0]
  have hresult : P = Polynomial.C β * B ^ d := by
    have hv := congrArg (MvPolynomial.aeval ![Polynomial.X, (1 : Polynomial K)]) he
    simp only [Polynomial.aeval_homogenize_X_one P hdegree, map_mul, map_pow,
      MvPolynomial.aeval_C, binary_linear_form_dehomogenize] at hv
    exact hv
  refine ⟨β, B, hβ, ?_, segreRulingAffineFactor_natDegree_le_one _, hresult⟩
  intro hz
  apply hP
  rw [hresult, hz, zero_pow hd.ne', mul_zero]

end DimensionFourDependence
