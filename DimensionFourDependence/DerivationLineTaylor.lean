import DimensionFourDependence.IsotropicQuadraticBaseChange

/-! # Integrating a zero-acceleration derivation to an actual polynomial line

If `D² y = 0`, every constant-coefficient relation of `y` vanishes on
`y+t Dy`. The coefficientwise derivation equals parameter differentiation
on this substitution; a coefficient recurrence replaces an infinite series.
-/

namespace DimensionFourDependence

open MvPolynomial

variable {K F : Type*} [Field K] [Field F] [Algebra K F] {n : ℕ}

/-- Apply a derivation to the coefficients of an ordinary polynomial. -/
noncomputable def polynomialCoefficientDerivation (D : Derivation K F F) :
    Derivation K (Polynomial F) (Polynomial F) :=
  PolynomialModule.equivPolynomialSelf.compDer D.mapCoeffs

@[simp]
theorem polynomialCoefficientDerivation_coeff (D : Derivation K F F) (p : Polynomial F) (i : ℕ) :
    (polynomialCoefficientDerivation D p).coeff i = D (p.coeff i) := rfl

@[simp]
theorem polynomialCoefficientDerivation_C (D : Derivation K F F) (a : F) :
    polynomialCoefficientDerivation D (Polynomial.C a) = Polynomial.C (D a) := by
  ext i
  simp only [polynomialCoefficientDerivation_coeff, Polynomial.coeff_C]
  split_ifs <;> simp

@[simp]
theorem polynomialCoefficientDerivation_X (D : Derivation K F F) :
    polynomialCoefficientDerivation D Polynomial.X = 0 := by
  ext i
  simp only [polynomialCoefficientDerivation_coeff, Polynomial.coeff_X, Polynomial.coeff_zero]
  split_ifs <;> simp

/-- On a line with constant velocity, coefficient differentiation equals
differentiation in the line parameter for every ground-field polynomial. -/
theorem aeval_line_coefficient_derivation (D : Derivation K F F) (y v : Fin n → F)
    (hy : ∀ i, D (y i) = v i) (hv : ∀ i, D (v i) = 0) (P : MvPolynomial (Fin n) K) :
    polynomialCoefficientDerivation D
      (aeval (fun i => Polynomial.C (y i) + Polynomial.C (v i) * Polynomial.X) P) =
    Polynomial.derivative
      (aeval (fun i => Polynomial.C (y i) + Polynomial.C (v i) * Polynomial.X) P) := by
  have hi (i : Fin n) : polynomialCoefficientDerivation D
      (Polynomial.C (y i) + Polynomial.C (v i) * Polynomial.X) =
      Polynomial.derivative (Polynomial.C (y i) + Polynomial.C (v i) * Polynomial.X) := by
    simp [Derivation.leibniz, smul_eq_mul, hy, hv]
  induction P using MvPolynomial.induction_on with
  | C a =>
    have hc : (aeval (fun i => Polynomial.C (y i) + Polynomial.C (v i) * Polynomial.X)) (C a) =
        Polynomial.C (algebraMap K F a) := by
      rw [aeval_C, IsScalarTower.algebraMap_apply K F (Polynomial F)]
      rfl
    rw [hc]
    simp
  | add P Q hP hQ => simp only [map_add, hP, hQ]
  | mul_X P i hP =>
    simp only [map_mul, aeval_X, Derivation.leibniz, Polynomial.derivative_mul, hP, hi, smul_eq_mul]
    ring

/-- The coefficient recurrence forces a polynomial solution of this
differential equation with zero constant term to vanish identically. -/
theorem polynomial_zero_of_coefficient_derivation_eq_derivative [CharZero F]
    (D : Derivation K F F) (p : Polynomial F)
    (hp : polynomialCoefficientDerivation D p = p.derivative) (h0 : p.coeff 0 = 0) : p = 0 := by
  apply Polynomial.ext
  intro i
  rw [Polynomial.coeff_zero]
  induction i with
  | zero => exact h0
  | succ i ih =>
    have he := congrArg (fun q : Polynomial F => q.coeff i) hp
    rw [polynomialCoefficientDerivation_coeff, Polynomial.coeff_derivative, ih, map_zero] at he
    have hn : (i : F) + 1 ≠ 0 := by
      simpa only [Nat.cast_add, Nat.cast_one] using
        (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero i) : ((i + 1 : ℕ) : F) ≠ 0)
    exact (mul_eq_zero.mp he.symm).resolve_right hn

/-- The exact Taylor-line identity used to integrate the direction in
Section 3.2. It holds for every relation, without a degree bound. -/
theorem relation_vanishes_on_zero_acceleration_line [CharZero F]
    (D : Derivation K F F) (y : Fin n → F) (hy : ∀ i, D (D (y i)) = 0)
    (P : MvPolynomial (Fin n) K) (hP : aeval y P = 0) :
    aeval (fun i => Polynomial.C (y i) + Polynomial.C (D (y i)) * Polynomial.X) P = 0 := by
  apply polynomial_zero_of_coefficient_derivation_eq_derivative D
  · exact aeval_line_coefficient_derivation D y (fun i => D (y i)) (fun _ => rfl) hy P
  · have hc (Q : MvPolynomial (Fin n) K) :
        ((aeval (fun i => Polynomial.C (y i) + Polynomial.C (D (y i)) * Polynomial.X)) Q).coeff 0 =
          aeval y Q := by
      induction Q using MvPolynomial.induction_on with
      | C a =>
        rw [aeval_C, IsScalarTower.algebraMap_apply K F (Polynomial F)]
        change (Polynomial.C (algebraMap K F a)).coeff 0 = aeval y (C a)
        simp
      | add Q R hQ hR => simp only [map_add, Polynomial.coeff_add, hQ, hR]
      | mul_X Q i hQ =>
        simp only [map_mul, aeval_X, Polynomial.mul_coeff_zero, hQ]
        simp
    exact (hc P).trans hP

end DimensionFourDependence
