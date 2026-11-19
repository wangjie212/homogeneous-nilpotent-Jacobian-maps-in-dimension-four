import DimensionFourDependence.CubicDifferentiation

/-! # Euler weight of a quadratic expression with varying coefficients -/

namespace DimensionFourDependence

variable {K F : Type*} [Field K] [Field F] [Algebra K F] {n : ℕ}

/-- Coefficient weights `r-1` and `r-2`, with coordinate weight one,
make the full affine-quadratic expression have weight `r`. -/
theorem quadraticExpression_euler_weight (D : Derivation K F F) (r : F)
    (a : Fin n → F) (T : Matrix (Fin n) (Fin n) F) (x : Fin n → F)
    (ha : ∀ i, D (a i) = (r - 1) * a i)
    (hT : ∀ i j, D (T i j) = (r - 2) * T i j)
    (hx : ∀ i, D (x i) = x i) :
    D (quadraticExpression a T x) = r * quadraticExpression a T x := by
  have hlin : D (∑ i, a i * x i) = r * ∑ i, a i * x i := by
    rw [map_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [D.leibniz, ha, hx]
    simp only [smul_eq_mul]
    ring
  have hquad : D (∑ i, ∑ j, T i j * x i * x j) = r * ∑ i, ∑ j, T i j * x i * x j := by
    rw [map_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [map_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [D.leibniz, D.leibniz, hT, hx, hx]
    simp only [smul_eq_mul]
    ring
  unfold quadraticExpression
  have htwo : D ((2 : F)⁻¹) = 0 := by
    simpa only [Nat.cast_ofNat] using derivation_inv_natCast_zero D 2
  rw [map_add, hlin, D.leibniz, htwo, smul_zero, add_zero, hquad]
  simp only [smul_eq_mul]
  ring

end DimensionFourDependence
