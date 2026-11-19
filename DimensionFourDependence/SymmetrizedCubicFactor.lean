import DimensionFourDependence.FiberPolynomialForms

/-! # Recovering a linear-times-quadratic cubic from its symmetric tensor -/

namespace DimensionFourDependence

open MvPolynomial Matrix

variable {E : Type*} [Field E] [CharZero E] {n : ℕ}

/-- A cubic tensor with the polarized linear-quadratic formula has
exactly that product as its original polynomial. No polynomial
factorization hypothesis or pointwise density argument is needed. -/
theorem cubicFormPolynomial_eq_linear_mul_quadratic_of_polarization
    (Λ : Fin n → E) (B : Matrix (Fin n) (Fin n) E)
    (T : Fin n → Fin n → Fin n → E)
    (hT : ∀ i j k, (3 : E) * T i j k =
      Λ i * B j k + Λ j * B i k + Λ k * B i j) :
    cubicFormPolynomial T = linearFormPolynomial Λ * quadraticFormPolynomial B := by
  classical
  let P := linearFormPolynomial Λ * quadraticFormPolynomial B
  have h₁ : (∑ i, ∑ j, ∑ k, C (Λ i * B j k) * X i * X j * X k) = P := by
    unfold P
    rw [linearFormPolynomial, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    simp only [quadraticFormPolynomial, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    rw [map_mul]
    ring
  have h₂ : (∑ i, ∑ j, ∑ k, C (Λ j * B i k) * X i * X j * X k) = P := by
    rw [Finset.sum_comm]
    convert h₁ using 1
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    ring
  have h₃ : (∑ i, ∑ j, ∑ k, C (Λ k * B i j) * X i * X j * X k) = P := by
    calc
      _ = ∑ i, ∑ k, ∑ j, C (Λ k * B i j) * X i * X j * X k := by
        apply Finset.sum_congr rfl
        intro i _
        exact Finset.sum_comm
      _ = ∑ k, ∑ i, ∑ j, C (Λ k * B i j) * X i * X j * X k := Finset.sum_comm
      _ = P := by
        convert h₁ using 1
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        apply Finset.sum_congr rfl
        intro k _
        ring
  have h3 : (C (3 : E) : MvPolynomial (Fin n) E) ≠ 0 := by simp
  apply mul_left_cancel₀ h3
  change C 3 * cubicFormPolynomial T = C 3 * P
  have he : C (3 : E) * cubicFormPolynomial T =
      ∑ i, ∑ j, ∑ k, C ((3 : E) * T i j k) * X i * X j * X k := by
    simp only [cubicFormPolynomial, Finset.mul_sum, map_mul]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [he]
  simp only [hT, map_add, add_mul, Finset.sum_add_distrib]
  rw [h₁, h₂, h₃]
  simp only [map_ofNat]
  ring

end DimensionFourDependence
