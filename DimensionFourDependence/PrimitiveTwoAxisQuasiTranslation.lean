import DimensionFourDependence.ClassifiedKernelCoordinateDependence

/-! # Primitivity and zero acceleration make a two-axis direction binary -/

namespace DimensionFourDependence

open MvPolynomial Matrix

set_option maxHeartbeats 2500000

variable {K : Type*} [Field K] [CharZero K]
local notation "R₀" => MvPolynomial (Fin 4) K

/-- In the primitive two-axis form, the two surviving entries are
relatively prime as polynomials in the entire original source. -/
theorem primitive_two_axis_entries_isRelPrime (A B : R₀)
    (hprim : IsPrimitiveVec (![0, 0, A, B] : Fin 4 → R₀)) : IsRelPrime A B := by
  intro p hpA hpB
  apply hprim p
  intro i
  fin_cases i <;> simp [hpA, hpB]

/-- Once two coordinates of a primitive homogeneous quasi-translation
vanish, zero acceleration itself removes both remaining source variables
from both entries. No binary-form hypothesis is required. -/
theorem primitive_two_axis_homogeneous_zero_acceleration_has_binary_entries
    (A B : R₀) {e : ℕ} (hA : A.IsHomogeneous e) (hB : B.IsHomogeneous e)
    (hprim : IsPrimitiveVec (![0, 0, A, B] : Fin 4 → R₀))
    (hacc : jac (![0, 0, A, B] : Fin 4 → R₀) *ᵥ ![0, 0, A, B] = 0) :
    pderiv 2 A = 0 ∧ pderiv 3 A = 0 ∧ pderiv 2 B = 0 ∧ pderiv 3 B = 0 := by
  have hrel := primitive_two_axis_entries_isRelPrime A B hprim
  have h2 := congrFun hacc 2
  have h3 := congrFun hacc 3
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, jac] at h2 h3
  change pderiv 2 A * A + pderiv 3 A * B = 0 at h2
  change pderiv 2 B * A + pderiv 3 B * B = 0 at h3
  have hAw : pderiv 3 A = 0 := by
    apply pderiv_eq_zero_of_dvd hA 3
    apply hrel.dvd_of_dvd_mul_left
    exact ⟨-pderiv 2 A, by linear_combination h2⟩
  have hBz : pderiv 2 B = 0 := by
    apply pderiv_eq_zero_of_dvd hB 2
    apply hrel.symm.dvd_of_dvd_mul_left
    exact ⟨-pderiv 3 B, by linear_combination h3⟩
  have hAz : pderiv 2 A = 0 := by
    by_cases hz : A = 0
    · simp [hz]
    · rw [hAw, zero_mul, add_zero] at h2
      exact (mul_eq_zero.mp h2).resolve_right hz
  have hBw : pderiv 3 B = 0 := by
    by_cases hz : B = 0
    · simp [hz]
    · rw [hBz, zero_mul, zero_add] at h3
      exact (mul_eq_zero.mp h3).resolve_right hz
  exact ⟨hAz, hAw, hBz, hBw⟩

/-- Only the two zero coordinates are needed from classification.
Primitivity, homogeneity and the actual zero-acceleration equation
construct the binary dependence of both surviving direction entries. -/
theorem primitive_positive_zero_acceleration_kernel_in_two_axis_coordinates_forces_original_componentsDependent
    (H : Fin 4 → R₀) {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d)
    (hN : IsNilpotent (jac H)) (u : Fin 4 → R₀) {e : ℕ}
    (hu : IsPrimRightKernel (jac H) u e) (he : 0 < e) (hacc : jac u *ᵥ u = 0)
    (T S : Matrix (Fin 4) (Fin 4) K) (hTS : T * S = 1) (hST : S * T = 1)
    (A B : R₀) (hform : linearPolynomialConjugate T S u = ![0, 0, A, B]) :
    ComponentsDependent H := by
  have hhom := linearPolynomialConjugate_homogeneous T S u hu.homog
  have hprim := linearPolynomialConjugate_preserves_primitive_vector T S hTS hST u hu.prim
  have hacc' := linearPolynomialConjugate_preserves_polynomial_right_kernel T S hTS u u hacc
  rw [hform] at hhom hprim hacc'
  obtain ⟨hAz, hAw, hBz, hBw⟩ :=
    primitive_two_axis_homogeneous_zero_acceleration_has_binary_entries A B (hhom 2) (hhom 3) hprim hacc'
  exact primitive_positive_kernel_in_binary_coordinates_forces_original_componentsDependent
    H hd hH hN u hu he T S hTS hST A B hform hAz hAw hBz hBw

end DimensionFourDependence
