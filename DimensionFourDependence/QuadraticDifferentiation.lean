import DimensionFourDependence.CoefficientChainRule

/-! # Differentiating the linear and quadratic fiber expressions -/

namespace DimensionFourDependence

open Matrix

variable {F : Type*} [Field F] {n : ℕ}

/-- The quadratic expression in (2.2), with its coefficient arrays explicit. -/
noncomputable def quadraticExpression (a : Fin n → F) (T : Matrix (Fin n) (Fin n) F)
    (x : Fin n → F) : F :=
  (∑ i, a i * x i) + (2 : F)⁻¹ * ∑ i, ∑ j, T i j * x i * x j

/-- Symmetry gives the factor of two in the derivative of a quadratic form. -/
theorem symmetric_quadratic_polarization [CharZero F]
    (T : Matrix (Fin n) (Fin n) F) (hT : ∀ i j, T i j = T j i)
    (x v : Fin n → F) :
    (2 : F)⁻¹ * (∑ i, ∑ j, T i j * (v i * x j + x i * v j)) =
      ∑ i, ∑ j, T i j * x j * v i := by
  have hs : (∑ i, ∑ j, T i j * (x i * v j)) =
      ∑ i, ∑ j, T i j * x j * v i := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [hT j i]
    ring
  have ht : (∑ i, ∑ j, T i j * (v i * x j)) =
      ∑ i, ∑ j, T i j * x j * v i := by
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  simp only [mul_add, Finset.sum_add_distrib]
  rw [hs, ht]
  field_simp
  ring

variable {K : Type*} [Field K] [Algebra K F]

/-- Differentiate the equation defining the first invariant. -/
theorem linear_fiber_equation_derivative (D : Derivation K F F)
    (x g : Fin n → F) (t c : F) (hc : c = t - ∑ i, g i * x i) :
    D t - ∑ i, g i * D (x i) = D c + ∑ i, D (g i) * x i := by
  have hd := congrArg D hc
  rw [map_sub, map_sum] at hd
  have hs : (∑ i, D (g i * x i)) =
      (∑ i, D (g i) * x i) + ∑ i, g i * D (x i) := by
    simp [D.leibniz, smul_eq_mul, Finset.sum_add_distrib, mul_comm]
  rw [hs] at hd
  linear_combination -hd

/-- With its coefficients held constant, the quadratic expression has
gradient `a + T x`, for a symmetric matrix `T`. -/
theorem quadraticExpression_deriv [CharZero F] (D : Derivation K F F)
    (a : Fin n → F) (T : Matrix (Fin n) (Fin n) F) (x : Fin n → F)
    (ha : ∀ i, D (a i) = 0) (hT : ∀ i j, D (T i j) = 0)
    (hsym : ∀ i j, T i j = T j i) :
    D (quadraticExpression a T x) =
      ∑ i, (a i + ∑ j, T i j * x j) * D (x i) := by
  have hd2 : D (2 : F) = 0 := by
    rw [show (2 : F) = 1 + 1 by norm_num, map_add, D.map_one_eq_zero, add_zero]
  have htwo : D ((2 : F)⁻¹) = 0 := by rw [D.leibniz_inv, hd2, smul_zero]
  have hlin : D (∑ i, a i * x i) = ∑ i, a i * D (x i) := by
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [D.leibniz, ha, smul_zero, add_zero]
    rfl
  have hquad : D (∑ i, ∑ j, T i j * x i * x j) =
      ∑ i, ∑ j, T i j * (D (x i) * x j + x i * D (x j)) := by
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [D.leibniz, D.leibniz, hT, smul_zero, add_zero]
    simp only [smul_eq_mul]
    ring
  unfold quadraticExpression
  rw [map_add, hlin, D.leibniz, htwo, smul_zero, add_zero, hquad]
  simp only [smul_eq_mul]
  rw [symmetric_quadratic_polarization T hsym]
  simp only [add_mul, Finset.sum_add_distrib, Finset.sum_mul]

end DimensionFourDependence
