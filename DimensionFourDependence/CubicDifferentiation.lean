import DimensionFourDependence.QuadraticDifferentiation

/-! # Differentiating the quadratic equation and the cubic invariant -/

namespace DimensionFourDependence

open Matrix

variable {F : Type*} [Field F] {n : ℕ}

/-- Reverse the outer and inner indices of a finite triple sum. -/
theorem triple_sum_reverse (f : Fin n → Fin n → Fin n → F) :
    (∑ i, ∑ j, ∑ k, f i j k) = ∑ k, ∑ j, ∑ i, f i j k := by
  calc
    (∑ i, ∑ j, ∑ k, f i j k) = ∑ j, ∑ i, ∑ k, f i j k := Finset.sum_comm
    _ = ∑ j, ∑ k, ∑ i, f i j k := by
      apply Finset.sum_congr rfl
      intro j _
      exact Finset.sum_comm
    _ = ∑ k, ∑ j, ∑ i, f i j k := Finset.sum_comm

/-- The cubic expression in (2.2), with all coefficient arrays explicit. -/
noncomputable def cubicExpression (a : Fin n → F) (C : Matrix (Fin n) (Fin n) F)
    (T : Fin n → Fin n → Fin n → F) (x : Fin n → F) : F :=
  (∑ i, a i * x i) - (2 : F)⁻¹ * (∑ i, ∑ j, C i j * x i * x j) -
    (6 : F)⁻¹ * ∑ i, ∑ j, ∑ k, T i j k * x i * x j * x k

/-- Symmetry turns the three differentiated positions of a cubic into
the factor `1/2` in its gradient. -/
theorem symmetric_cubic_polarization [CharZero F]
    (T : Fin n → Fin n → Fin n → F)
    (h12 : ∀ i j k, T i j k = T j i k) (h23 : ∀ i j k, T i j k = T i k j)
    (x v : Fin n → F) :
    (6 : F)⁻¹ * (∑ i, ∑ j, ∑ k, T i j k *
      (v i * x j * x k + x i * v j * x k + x i * x j * v k)) =
      (2 : F)⁻¹ * ∑ i, ∑ j, ∑ k, T i j k * x j * x k * v i := by
  have h13 (i j k) : T i j k = T k j i :=
    (h12 i j k).trans ((h23 j i k).trans (h12 j k i))
  have h1 : (∑ i, ∑ j, ∑ k, T i j k * (v i * x j * x k)) =
      ∑ i, ∑ j, ∑ k, T i j k * x j * x k * v i := by
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    ring
  have h2 : (∑ i, ∑ j, ∑ k, T i j k * (x i * v j * x k)) =
      ∑ i, ∑ j, ∑ k, T i j k * x j * x k * v i := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    rw [h12 j i k]
    ring
  have h3 : (∑ i, ∑ j, ∑ k, T i j k * (x i * x j * v k)) =
      ∑ i, ∑ j, ∑ k, T i j k * x j * x k * v i := by
    rw [triple_sum_reverse]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    rw [h13 k j i]
    ring
  simp only [mul_add, Finset.sum_add_distrib]
  rw [h1, h2, h3]
  field_simp
  ring

variable {K : Type*} [Field K] [Algebra K F]

/-- Every derivation annihilates the inverse of a natural-number scalar. -/
theorem derivation_inv_natCast_zero (D : Derivation K F F) (m : ℕ) :
    D ((m : F)⁻¹) = 0 := by rw [D.leibniz_inv, D.map_natCast, smul_zero]

/-- Differentiate a quadratic expression while allowing its coefficients
to vary. The additional terms are the coefficient derivatives. -/
theorem quadraticExpression_deriv_full [CharZero F] (D : Derivation K F F)
    (a : Fin n → F) (T : Matrix (Fin n) (Fin n) F) (x : Fin n → F)
    (hsym : ∀ i j, T i j = T j i) :
    D (quadraticExpression a T x) =
      (∑ i, (a i + ∑ j, T i j * x j) * D (x i)) +
      (∑ i, D (a i) * x i) + (2 : F)⁻¹ * ∑ i, ∑ j, D (T i j) * x i * x j := by
  have htwo : D ((2 : F)⁻¹) = 0 := by
    simpa only [Nat.cast_ofNat] using derivation_inv_natCast_zero D 2
  have hlin : D (∑ i, a i * x i) =
      (∑ i, D (a i) * x i) + ∑ i, a i * D (x i) := by
    simp [D.leibniz, smul_eq_mul, Finset.sum_add_distrib, mul_comm, add_comm]
  have hentry (i j) : D (T i j * x i * x j) =
      D (T i j) * x i * x j + T i j * (D (x i) * x j + x i * D (x j)) := by
    simp only [D.leibniz, smul_eq_mul]
    ring
  have hquad : D (∑ i, ∑ j, T i j * x i * x j) =
      (∑ i, ∑ j, D (T i j) * x i * x j) +
        ∑ i, ∑ j, T i j * (D (x i) * x j + x i * D (x j)) := by
    simp only [map_sum, hentry, Finset.sum_add_distrib]
  unfold quadraticExpression
  rw [map_add, hlin, D.leibniz, htwo, smul_zero, add_zero, hquad]
  simp only [smul_eq_mul]
  rw [mul_add]
  rw [symmetric_quadratic_polarization T hsym]
  simp only [add_mul, Finset.sum_add_distrib, Finset.sum_mul]
  ring

/-- With coefficients held constant, the cubic expression has precisely
the gradient used for the third covector of Lemma 2.2. -/
theorem cubicExpression_deriv [CharZero F] (D : Derivation K F F)
    (a : Fin n → F) (C : Matrix (Fin n) (Fin n) F)
    (T : Fin n → Fin n → Fin n → F) (x : Fin n → F)
    (ha : ∀ i, D (a i) = 0) (hC : ∀ i j, D (C i j) = 0)
    (hT : ∀ i j k, D (T i j k) = 0) (hCsym : ∀ i j, C i j = C j i)
    (h12 : ∀ i j k, T i j k = T j i k) (h23 : ∀ i j k, T i j k = T i k j) :
    D (cubicExpression a C T x) = ∑ i,
      (a i - (∑ j, C i j * x j) - (2 : F)⁻¹ * ∑ j, ∑ k, T i j k * x j * x k) * D (x i) := by
  have hsix : D ((6 : F)⁻¹) = 0 := by
    simpa only [Nat.cast_ofNat] using derivation_inv_natCast_zero D 6
  have hlin : D (∑ i, a i * x i) = ∑ i, a i * D (x i) := by
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [D.leibniz, ha, smul_zero, add_zero]
    rfl
  have hquad : D ((2 : F)⁻¹ * ∑ i, ∑ j, C i j * x i * x j) =
      ∑ i, (∑ j, C i j * x j) * D (x i) := by
    simpa only [quadraticExpression, zero_mul, Finset.sum_const_zero, zero_add] using
      quadraticExpression_deriv D (fun _ => 0) C x (fun _ => map_zero D) hC hCsym
  have hentry (i j k) : D (T i j k * x i * x j * x k) =
      T i j k * (D (x i) * x j * x k + x i * D (x j) * x k + x i * x j * D (x k)) := by
    simp only [D.leibniz, hT, smul_eq_mul]
    ring
  have hcub : D (∑ i, ∑ j, ∑ k, T i j k * x i * x j * x k) =
      ∑ i, ∑ j, ∑ k, T i j k *
        (D (x i) * x j * x k + x i * D (x j) * x k + x i * x j * D (x k)) := by
    simp only [map_sum, hentry]
  unfold cubicExpression
  rw [map_sub, map_sub, hlin, hquad, D.leibniz, hsix, smul_zero, add_zero, hcub]
  simp only [smul_eq_mul]
  rw [symmetric_cubic_polarization T h12 h23]
  simp only [sub_mul, Finset.sum_sub_distrib, Finset.sum_mul, Finset.mul_sum, mul_assoc]

end DimensionFourDependence
