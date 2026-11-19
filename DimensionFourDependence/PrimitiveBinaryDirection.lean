import DimensionFourDependence.Homogeneous

/-! # A primitive positive binary direction has nonzero entries and Wronskian -/

namespace DimensionFourDependence

open MvPolynomial

set_option maxHeartbeats 2000000

variable {K : Type*} [Field K] [CharZero K]
local notation "R₀" => MvPolynomial (Fin 4) K

/-- A positive-degree homogeneous polynomial cannot be a unit. -/
theorem positive_homogeneous_polynomial_not_isUnit (P : R₀) {e : ℕ}
    (he : 0 < e) (hP : P.IsHomogeneous e) : ¬IsUnit P := by
  intro hu
  have hz := (MvPolynomial.isUnit_iff_totalDegree_of_isReduced.mp hu).2
  rw [hP.totalDegree hu.ne_zero] at hz
  omega

/-- Primitivity and positive homogeneity of an actual direction
(0,0,A(x,y),B(x,y)) construct both nonzero entries and the nonzero binary
Wronskian. No nonconstant-ratio or Wronskian hypothesis is supplied. -/
theorem primitive_positive_binary_direction_entries_and_wronskian_nonzero
    (A B : R₀) {e : ℕ} (he : 0 < e)
    (hA : A.IsHomogeneous e) (hB : B.IsHomogeneous e)
    (hprim : IsPrimitiveVec (![0, 0, A, B] : Fin 4 → R₀))
    (hAz : pderiv 2 A = 0) (hAw : pderiv 3 A = 0)
    (hBz : pderiv 2 B = 0) (hBw : pderiv 3 B = 0) :
    A ≠ 0 ∧ B ≠ 0 ∧
      (fun i : Fin 2 => B * pderiv (i.castAdd 2) A - A * pderiv (i.castAdd 2) B) ≠ 0 := by
  have hA0 : A ≠ 0 := by
    intro hz
    apply positive_homogeneous_polynomial_not_isUnit B he hB
    apply hprim B
    intro i
    fin_cases i <;> simp [hz]
  have hB0 : B ≠ 0 := by
    intro hz
    apply positive_homogeneous_polynomial_not_isUnit A he hA
    apply hprim A
    intro i
    fin_cases i <;> simp [hz]
  refine ⟨hA0, hB0, ?_⟩
  intro hwr
  have h0 := congrFun hwr 0
  have h1 := congrFun hwr 1
  change B * pderiv 0 A - A * pderiv 0 B = 0 at h0
  change B * pderiv 1 A - A * pderiv 1 B = 0 at h1
  have hgrad (i : Fin 4) : A * pderiv i B = B * pderiv i A := by
    fin_cases i
    · change A * pderiv (0 : Fin 4) B = B * pderiv 0 A
      linear_combination -h0
    · change A * pderiv (1 : Fin 4) B = B * pderiv 1 A
      linear_combination -h1
    · change A * pderiv (2 : Fin 4) B = B * pderiv 2 A
      simp only [hAz, hBz, mul_zero]
    · change A * pderiv (3 : Fin 4) B = B * pderiv 3 A
      simp only [hAw, hBw, mul_zero]
  obtain ⟨c, hc⟩ := proportional_of_wronskian hA hB hA0 hgrad
  apply positive_homogeneous_polynomial_not_isUnit A he hA
  apply hprim A
  intro i
  fin_cases i
  · simp
  · simp
  · exact dvd_rfl
  · change A ∣ B
    rw [hc, smul_eq_C_mul]
    exact dvd_mul_left _ _

end DimensionFourDependence
