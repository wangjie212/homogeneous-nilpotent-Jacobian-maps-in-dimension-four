import DimensionFourDependence.FiniteCovectorOrbitFrame
import DimensionFourDependence.TernaryPencilOrbitMinor

/-! # One actual ternary frame simultaneously avoids a finite covector family -/

namespace DimensionFourDependence

open Matrix MvPolynomial

set_option maxHeartbeats 4000000

variable {K : Type*} [Field K] [CharZero K]
local notation "R₀" => MvPolynomial (Fin 3) K

theorem ternary_finite_nonzero_covector_orbit_minors_construct_actual_source_point
    (H : Fin 3 → R₀) (hW : jac H ^ 2 *ᵥ coordVec ≠ 0)
    (F : Finset ((Fin 3 → K) × (Fin 3 → K)))
    (hF : ∀ c ∈ F,
      outputLinearCombination H c.1 * outputLinearCombination (jac H *ᵥ H) c.2 -
        outputLinearCombination H c.2 * outputLinearCombination (jac H *ᵥ H) c.1 ≠ 0) :
    ∃ x : Fin 3 → K, ((jac H).map (aeval x)) ^ 2 *ᵥ x ≠ 0 ∧
      ∀ c ∈ F, aeval x
        (outputLinearCombination H c.1 * outputLinearCombination (jac H *ᵥ H) c.2 -
          outputLinearCombination H c.2 * outputLinearCombination (jac H *ᵥ H) c.1) ≠ 0 := by
  obtain ⟨i, hi⟩ : ∃ i, (jac H ^ 2 *ᵥ coordVec) i ≠ 0 := by
    simpa only [ne_eq, _root_.funext_iff, Pi.zero_apply, not_forall] using hW
  obtain ⟨x, hx, hminors⟩ :=
    finite_nonzero_source_polynomials_construct_simultaneous_nonzero_point F _ hF _ hi
  refine ⟨x, ?_, hminors⟩
  intro hz
  have he := congrFun ((polynomial_jacobian_second_euler_iterate_point_value H x).trans hz) i
  exact hx (by simpa only [Pi.zero_apply] using he)

/-- Every finite collection of constant covector pairs with nonzero
actual source minors admits a single normalized coordinate frame in
which every pair has nonzero determinant on columns one and two.
The source point and inverse coordinate matrices are constructed. -/
theorem ternary_finite_nonzero_covector_orbit_minors_construct_normalized_avoiding_frame
    (H : Fin 3 → R₀) {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d)
    (hN : IsNilpotent (jac H)) (hW : jac H ^ 2 *ᵥ coordVec ≠ 0)
    (F : Finset ((Fin 3 → K) × (Fin 3 → K)))
    (hF : ∀ c ∈ F,
      outputLinearCombination H c.1 * outputLinearCombination (jac H *ᵥ H) c.2 -
        outputLinearCombination H c.2 * outputLinearCombination (jac H *ᵥ H) c.1 ≠ 0) :
    ∃ T S : Matrix (Fin 3) (Fin 3) K, T * S = 1 ∧ S * T = 1 ∧
      (∀ i, aeval (Pi.single (0 : Fin 3) (1 : K))
        (pderiv 0 (linearPolynomialConjugate T S H i)) = if i = 1 then 1 else 0) ∧
      (∀ i, aeval (Pi.single (0 : Fin 3) (1 : K))
        (pderiv 1 (linearPolynomialConjugate T S H i)) = if i = 2 then 1 else 0) ∧
      ∀ c ∈ F,
        (∑ i, c.1 i * T i 1) * (∑ i, c.2 i * T i 2) -
          (∑ i, c.2 i * T i 1) * (∑ i, c.1 i * T i 2) ≠ 0 := by
  obtain ⟨x, hx, hminors⟩ :=
    ternary_finite_nonzero_covector_orbit_minors_construct_actual_source_point H hW F hF
  obtain ⟨T, S, hTS, hST, _hcol0, hcol1, hcol2, hj0, hj1⟩ :=
    nilpotent_ternary_jacobian_point_constructs_normalized_three_column_coordinates H hN x hx
  obtain ⟨he1, he2⟩ := homogeneous_jacobian_point_orbit_output_acceleration H hH x
  have hpair1 (μ : Fin 3 → K) : (∑ i, μ i * T i 1) = (d : K) * aeval x (outputLinearCombination H μ) := by
    simp only [hcol1, he1, Pi.smul_apply, smul_eq_mul, outputLinearCombination,
      map_sum, map_mul, aeval_C, Algebra.algebraMap_self, RingHom.id_apply, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hpair2 (μ : Fin 3 → K) :
      (∑ i, μ i * T i 2) = (d : K) * aeval x (outputLinearCombination (jac H *ᵥ H) μ) := by
    simp only [hcol2, he2, Pi.smul_apply, smul_eq_mul, outputLinearCombination,
      map_sum, map_mul, aeval_C, Algebra.algebraMap_self, RingHom.id_apply, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  refine ⟨T, S, hTS, hST, hj0, hj1, ?_⟩
  intro c hc
  have hdet :
      (∑ i, c.1 i * T i 1) * (∑ i, c.2 i * T i 2) -
        (∑ i, c.2 i * T i 1) * (∑ i, c.1 i * T i 2) =
      (d : K) ^ 2 * aeval x
        (outputLinearCombination H c.1 * outputLinearCombination (jac H *ᵥ H) c.2 -
          outputLinearCombination H c.2 * outputLinearCombination (jac H *ᵥ H) c.1) := by
    rw [hpair1, hpair2, hpair1, hpair2]
    simp only [map_sub, map_mul]
    ring
  rw [hdet]
  exact mul_ne_zero (pow_ne_zero 2 (Nat.cast_ne_zero.mpr hd.ne')) (hminors c hc)


end DimensionFourDependence
