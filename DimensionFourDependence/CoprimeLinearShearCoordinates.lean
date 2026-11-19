import DimensionFourDependence.LinearTameConjugacy

/-! # Coprime homogeneous linear forms are independent coefficient coordinates -/

namespace DimensionFourDependence.Shear

open Matrix MvPolynomial

variable {K : Type*} [Field K]
local notation "R₂" => MvPolynomial (Fin 2) K

/-- A nonzero homogeneous linear form over a field has degree one
and cannot be a unit. -/
theorem nonzero_homogeneous_linear_coefficient_not_isUnit
    (a : R₂) (ha : a.IsHomogeneous 1) (hne : a ≠ 0) : ¬IsUnit a := by
  intro hu
  have h := (isUnit_iff_totalDegree_of_isReduced.mp hu).2
  rw [ha.totalDegree hne] at h
  omega

/-- The two forms supply their actual constant coefficient matrix,
whose determinant is nonzero by relative primality. -/
theorem coprime_homogeneous_linear_coefficients_construct_frame
    (a b : R₂) (ha : a.IsHomogeneous 1) (hb : b.IsHomogeneous 1)
    (hcop : IsRelPrime a b) :
    ∃ T : Matrix (Fin 2) (Fin 2) K, IsUnit T.det ∧
      a = linearPolynomialMap T 0 ∧ b = linearPolynomialMap T 1 := by
  have hne (p q : R₂) (hq : q.IsHomogeneous 1) (hpq : IsRelPrime p q) : p ≠ 0 := by
    intro hz
    have hu := hpq (show q ∣ p by simp [hz]) (dvd_refl q)
    have h := (isUnit_iff_totalDegree_of_isReduced.mp hu).2
    rw [hq.totalDegree hu.ne_zero] at h
    omega
  have ha0 := hne a b hb hcop
  let T : Matrix (Fin 2) (Fin 2) K := fun i j => (pderiv j (![a,b] i)).coeff 0
  have hA : a = linearPolynomialMap T 0 := eq_sum_of_isHomogeneous_one ha
  have hB : b = linearPolynomialMap T 1 := eq_sum_of_isHomogeneous_one hb
  refine ⟨T, isUnit_iff_ne_zero.mpr ?_, hA, hB⟩
  intro hd
  obtain ⟨c, hc, hT⟩ := Matrix.exists_vecMul_eq_zero_iff.mpr hd
  have hzero : C (c 0) * a + C (c 1) * b = 0 := by
    rw [hA, hB]
    simp only [linearPolynomialMap, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_eq_zero
    intro j _
    have hj := congrFun hT j
    change (∑ i : Fin 2, c i * T i j) = 0 at hj
    rw [Fin.sum_univ_two] at hj
    calc
      C (c 0) * (C (T 0 j) * X j) + C (c 1) * (C (T 1 j) * X j) =
          C (c 0 * T 0 j + c 1 * T 1 j) * X j := by simp only [map_add, map_mul]; ring
      _ = 0 := by rw [hj, map_zero, zero_mul]
  have hc1 : c 1 ≠ 0 := by
    intro hz
    have h0 : c 0 = 0 := by
      have hp : C (c 0) * a = 0 := by simpa [hz] using hzero
      exact C_injective (Fin 2) K (by simpa using (mul_eq_zero.mp hp).resolve_right ha0)
    apply hc
    funext i
    fin_cases i <;> assumption
  have hh : b = a * C (-(c 0) / c 1) := by
    apply (mul_left_cancel₀ (show (C (c 1) : R₂) ≠ 0 from C_ne_zero.mpr hc1))
    calc
      C (c 1) * b = -(C (c 0) * a) := eq_neg_of_add_eq_zero_right hzero
      _ = C (c 1) * (a * C (-(c 0) / c 1)) := by
        rw [mul_left_comm, ← map_mul, mul_div_cancel₀ _ hc1, map_neg]
        ring
  exact nonzero_homogeneous_linear_coefficient_not_isUnit a ha ha0
    (hcop (dvd_refl a) ⟨_, hh⟩)

end DimensionFourDependence.Shear
