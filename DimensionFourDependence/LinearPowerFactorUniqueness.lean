import DimensionFourDependence.LinearPowerCoefficientDescent

/-! # Pure linear powers determine their projective factors uniquely

The coordinate-point gradient ratio identifies the normalized covector.
Thus equality of nonzero scalar linear powers makes their covectors
proportional, with a constructed nonzero scalar.
-/

namespace DimensionFourDependence

open MvPolynomial

variable {F : Type*} [Field F] [CharZero F] {n : ℕ}

/-- The coordinate-point gradient ratio exactly recovers every
coefficient ratio of a nonzero scalar linear power. -/
theorem linear_power_coefficient_ratio_formula
    (P : MvPolynomial (Fin n) F) {d : ℕ} (hd : 0 < d)
    (a : Fin n → F) (c : F) (hc : c ≠ 0) (j : Fin n) (hj : a j ≠ 0)
    (hP : P = C c * linearFormPolynomial a ^ d) (i : Fin n) :
    a i / a j = MvPolynomial.eval (Pi.single j 1) (pderiv i P) /
      ((d : F) * MvPolynomial.eval (Pi.single j 1) P) := by
  have hdegree : (d : F) ≠ 0 := by exact_mod_cast hd.ne'
  rw [hP, linear_power_gradient_coordinate_value]
  simp only [map_mul, eval_C, map_pow, linearFormPolynomial_eval_coordinate_point]
  have hpow : a j ^ d = a j ^ (d - 1) * a j := by
    rw [← pow_succ, Nat.sub_add_cancel hd]
  rw [hpow]
  field_simp [hc, hj, hdegree]

/-- Equality of nonzero scalar linear powers constructs the common
projective covector scalar, retaining all original coordinate labels. -/
theorem equal_nonzero_scaled_linear_powers_covectors_proportional
    {d : ℕ} (hd : 0 < d) (a b : Fin n → F) (α β : F) (hβ : β ≠ 0)
    (j : Fin n) (hj : b j ≠ 0)
    (h : C α * linearFormPolynomial a ^ d = C β * linearFormPolynomial b ^ d) :
    ∃ s : F, s ≠ 0 ∧ ∀ i, a i = s * b i := by
  classical
  have hvalue := congrArg (MvPolynomial.eval (Pi.single j 1)) h
  simp only [map_mul, eval_C, map_pow, linearFormPolynomial_eval_coordinate_point] at hvalue
  have hright : β * b j ^ d ≠ 0 := mul_ne_zero hβ (pow_ne_zero d hj)
  have hα : α ≠ 0 := by intro hz; rw [hz, zero_mul] at hvalue; exact hright hvalue.symm
  have haj : a j ≠ 0 := by
    intro hz
    rw [hz, zero_pow (Nat.ne_of_gt hd), mul_zero] at hvalue
    exact hright hvalue.symm
  refine ⟨a j / b j, div_ne_zero haj hj, ?_⟩
  intro i
  have ha := linear_power_coefficient_ratio_formula (C α * linearFormPolynomial a ^ d) hd a α hα j haj rfl i
  have hb := linear_power_coefficient_ratio_formula (C α * linearFormPolynomial a ^ d) hd b β hβ j hj h i
  have hcross := (div_eq_div_iff haj hj).mp (ha.trans hb.symm)
  rw [div_mul_eq_mul_div]
  exact (eq_div_iff hj).mpr (hcross.trans (mul_comm _ _))

end DimensionFourDependence
