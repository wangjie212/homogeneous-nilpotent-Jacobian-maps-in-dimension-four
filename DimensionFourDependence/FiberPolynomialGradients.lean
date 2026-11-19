import DimensionFourDependence.FiberPolynomialForms

/-! # Polynomial gradients of the quadratic and cubic fiber equations -/

namespace DimensionFourDependence

open MvPolynomial Matrix

variable {F : Type*} [Field F] {n : ℕ}

theorem linearFormPolynomial_pderiv (a : Fin n → F) (i : Fin n) :
    pderiv i (linearFormPolynomial a) = C (a i) := by
  simp [linearFormPolynomial, pderiv_X, Pi.single_apply]

/-- The affine equation is a graph hyperplane with unit last coefficient. -/
theorem affineFiberPolynomial_pderiv_last (g : Fin n → F) (c : F) :
    pderiv (Fin.last n) (affineFiberPolynomial g c) = 1 := by
  simp [affineFiberPolynomial, pderiv_X]

/-- Differentiate the quadratic coefficient array before using symmetry. -/
theorem quadraticFormPolynomial_pderiv (T : Matrix (Fin n) (Fin n) F) (i : Fin n) :
    pderiv i (quadraticFormPolynomial T) =
      (∑ j, C (T i j) * X j) + ∑ j, C (T j i) * X j := by
  simp [quadraticFormPolynomial, pderiv_X, Pi.single_apply,
    Finset.sum_add_distrib, add_comm, mul_comm]

theorem quadraticFormPolynomial_pderiv_symmetric (T : Matrix (Fin n) (Fin n) F)
    (hT : ∀ i j, T i j = T j i) (i : Fin n) :
    pderiv i (quadraticFormPolynomial T) = 2 * ∑ j, C (T i j) * X j := by
  rw [quadraticFormPolynomial_pderiv]
  have hs : (∑ j, C (T j i) * X j) = ∑ j, C (T i j) * X j := by
    apply Finset.sum_congr rfl
    intro j _
    rw [hT j i]
  rw [hs, ← two_mul]

/-- The three differentiated positions in a cubic coefficient array. -/
theorem cubicFormPolynomial_pderiv (T : Fin n → Fin n → Fin n → F) (i : Fin n) :
    pderiv i (cubicFormPolynomial T) =
      (∑ j, ∑ k, C (T i j k) * X j * X k) +
      (∑ j, ∑ k, C (T j i k) * X j * X k) +
        ∑ j, ∑ k, C (T j k i) * X j * X k := by
  have hentry (j k l : Fin n) : pderiv i (C (T j k l) * X j * X k * X l) =
      (if j = i then C (T j k l) * X k * X l else 0) +
      (if k = i then C (T j k l) * X j * X l else 0) +
        (if l = i then C (T j k l) * X j * X k else 0) := by
    by_cases hj : j = i <;> by_cases hk : k = i <;> by_cases hl : l = i <;>
      simp [pderiv_X, hj, hk, hl] <;> ring
  simp only [cubicFormPolynomial, map_sum, hentry, Finset.sum_add_distrib]
  simp

theorem cubicFormPolynomial_pderiv_symmetric (T : Fin n → Fin n → Fin n → F)
    (h12 : ∀ i j k, T i j k = T j i k) (h23 : ∀ i j k, T i j k = T i k j)
    (i : Fin n) :
    pderiv i (cubicFormPolynomial T) = 3 * ∑ j, ∑ k, C (T i j k) * X j * X k := by
  rw [cubicFormPolynomial_pderiv]
  have h2 : (∑ j, ∑ k, C (T j i k) * X j * X k) =
      ∑ j, ∑ k, C (T i j k) * X j * X k := by
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    rw [h12 j i k]
  have h3 : (∑ j, ∑ k, C (T j k i) * X j * X k) =
      ∑ j, ∑ k, C (T i j k) * X j * X k := by
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    rw [h23 j k i, h12 j i k]
  rw [h2, h3]
  ring

variable [CharZero F]

/-- The formal gradient of the quadratic fiber polynomial. -/
theorem quadraticFiberPolynomial_pderiv (a : Fin n → F) (T : Matrix (Fin n) (Fin n) F)
    (q : F) (hT : ∀ i j, T i j = T j i) (i : Fin n) :
    pderiv i (quadraticFiberPolynomial a T q) = C (a i) + ∑ j, C (T i j) * X j := by
  have hc : (C ((2 : F)⁻¹) : MvPolynomial (Fin n) F) * 2 = 1 := by
    rw [show (2 : MvPolynomial (Fin n) F) = C (2 : F) by simp [map_ofNat], ← map_mul]
    norm_num
  simp only [quadraticFiberPolynomial, map_sub, map_add, linearFormPolynomial_pderiv,
    pderiv_C_mul, quadraticFormPolynomial_pderiv_symmetric T hT, pderiv_C, sub_zero]
  rw [← mul_assoc, hc, one_mul]

/-- The formal gradient of the cubic fiber polynomial. -/
theorem cubicFiberPolynomial_pderiv (a : Fin n → F) (S : Matrix (Fin n) (Fin n) F)
    (T : Fin n → Fin n → Fin n → F) (k : F) (hS : ∀ i j, S i j = S j i)
    (h12 : ∀ i j l, T i j l = T j i l) (h23 : ∀ i j l, T i j l = T i l j) (i : Fin n) :
    pderiv i (cubicFiberPolynomial a S T k) =
      C (a i) - (∑ j, C (S i j) * X j) -
        C ((2 : F)⁻¹) * ∑ j, ∑ l, C (T i j l) * X j * X l := by
  have hc2 : (C ((2 : F)⁻¹) : MvPolynomial (Fin n) F) * 2 = 1 := by
    rw [show (2 : MvPolynomial (Fin n) F) = C (2 : F) by simp [map_ofNat], ← map_mul]
    norm_num
  have hc6 : (C ((6 : F)⁻¹) : MvPolynomial (Fin n) F) * 3 = C ((2 : F)⁻¹) := by
    rw [show (3 : MvPolynomial (Fin n) F) = C (3 : F) by simp [map_ofNat], ← map_mul]
    congr 1
    field_simp
    ring
  simp only [cubicFiberPolynomial, map_sub, linearFormPolynomial_pderiv,
    pderiv_C_mul, quadraticFormPolynomial_pderiv_symmetric S hS,
    cubicFormPolynomial_pderiv_symmetric T h12 h23, pderiv_C, sub_zero]
  rw [← mul_assoc, hc2, one_mul, ← mul_assoc, hc6]

variable {A : Type*} [Field A] [Algebra F A]

theorem quadraticFiberPolynomial_gradient_aeval (a : Fin n → F)
    (T : Matrix (Fin n) (Fin n) F) (q : F) (hT : ∀ i j, T i j = T j i)
    (x : Fin n → A) (i : Fin n) :
    aeval x (pderiv i (quadraticFiberPolynomial a T q)) =
      algebraMap F A (a i) + ∑ j, algebraMap F A (T i j) * x j := by
  rw [quadraticFiberPolynomial_pderiv a T q hT]
  simp

theorem cubicFiberPolynomial_gradient_aeval (a : Fin n → F) (S : Matrix (Fin n) (Fin n) F)
    (T : Fin n → Fin n → Fin n → F) (k : F) (hS : ∀ i j, S i j = S j i)
    (h12 : ∀ i j l, T i j l = T j i l) (h23 : ∀ i j l, T i j l = T i l j)
    (x : Fin n → A) (i : Fin n) :
    aeval x (pderiv i (cubicFiberPolynomial a S T k)) =
      algebraMap F A (a i) - (∑ j, algebraMap F A (S i j) * x j) -
        (2 : A)⁻¹ * ∑ j, ∑ l, algebraMap F A (T i j l) * x j * x l := by
  rw [cubicFiberPolynomial_pderiv a S T k hS h12 h23]
  simp [map_ofNat]

end DimensionFourDependence
