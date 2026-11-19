import DimensionFourDependence.HomogenizedParameterSourceJets
import DimensionFourDependence.TernaryNormalizedPointFrame

/-! # Normalized Jacobian columns construct the actual source pencil's first-order data -/

namespace DimensionFourDependence

open MvPolynomial Matrix

set_option maxHeartbeats 3000000

variable {K : Type*} [Field K]
local notation "R₀" => MvPolynomial (Fin 3) K

/-- Euler's identity turns the normalized first Jacobian column into
the complete original homogeneous output value at the first point. -/
theorem ternary_normalized_first_jacobian_column_constructs_homogeneous_point_values
    (H : Fin 3 → R₀) {d : ℕ} (hH : IsHomogMap H d)
    (hcol : ∀ i, aeval (Pi.single (0 : Fin 3) (1 : K)) (pderiv 0 (H i)) =
      if i = 1 then 1 else 0) :
    ∀ i, (d : K) * aeval (Pi.single (0 : Fin 3) (1 : K)) (H i) = if i = 1 then 1 else 0 := by
  classical
  intro i
  have he := congrArg (aeval (Pi.single (0 : Fin 3) (1 : K))) (hH i).sum_X_mul_pderiv
  have he' : (d : K) * aeval (Pi.single (0 : Fin 3) (1 : K)) (H i) =
      aeval (Pi.single (0 : Fin 3) (1 : K)) (pderiv 0 (H i)) := by
    simpa [map_sum, map_mul, Pi.single_apply, nsmul_eq_mul] using he.symm
  exact he'.trans (hcol i)

variable [CharZero K]

/-- The actual normalized output has one nonzero coordinate and all
other coordinates zero, over the original characteristic-zero field. -/
theorem ternary_normalized_first_jacobian_column_output_support_and_nonzero
    (H : Fin 3 → R₀) {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d)
    (hcol : ∀ i, aeval (Pi.single (0 : Fin 3) (1 : K)) (pderiv 0 (H i)) =
      if i = 1 then 1 else 0) :
    (∀ i, i ≠ 1 → aeval (Pi.single (0 : Fin 3) (1 : K)) (H i) = 0) ∧
      aeval (Pi.single (0 : Fin 3) (1 : K)) (H 1) ≠ 0 := by
  have he := ternary_normalized_first_jacobian_column_constructs_homogeneous_point_values H hH hcol
  have hdK : (d : K) ≠ 0 := by exact_mod_cast hd.ne'
  constructor
  · intro i hi
    have h := he i
    rw [if_neg hi] at h
    exact (mul_eq_zero.mp h).resolve_left hdK
  · intro hz
    have h := he 1
    simp only [hz, mul_zero, if_pos rfl] at h
    exact zero_ne_one h

omit [CharZero K] in
/-- A normalized source pencil and the original first two output
columns construct a nonzero first source derivative of its numerator.
The inactive parameter entry has zero first-order coefficient,
and the corresponding original output has the full common factor
times the square numerator as a divisor. -/
theorem ternary_normalized_parameter_output_jets_construct_nonzero_pencil_derivative_and_square_divisor
    (H : Fin 3 → R₀) (p q g : R₀) (z : Fin 3 → K)
    (hp : aeval z p = 0) (hq : aeval z q = 1) (hg : aeval z g ≠ 0)
    (v : Fin 3 → Polynomial K) {N : ℕ} (hN : ∀ i, (v i).natDegree ≤ N)
    (hfactor : ∀ i, H i = g * homogeneousParameterPolynomialValue (v i) N p q)
    (hvalue : ∀ i, i ≠ 1 → aeval z (H i) = 0)
    (hder : ∀ i, aeval z (pderiv 1 (H i)) = if i = 2 then 1 else 0) :
    aeval z (pderiv 1 p) ≠ 0 ∧
      (∀ i, i ≠ 1 → (v i).coeff 0 = 0) ∧
      (v 0).coeff 1 = 0 ∧ g * p ^ 2 ∣ H 0 := by
  classical
  have hWvalue (i) := homogeneous_parameter_value_at_normalized_source_point (v i) (hN i) p q z hp hq
  have hc0 (i : Fin 3) (hi : i ≠ 1) : (v i).coeff 0 = 0 := by
    have he := congrArg (aeval z) (hfactor i)
    rw [map_mul, hWvalue, hvalue i hi] at he
    exact (mul_eq_zero.mp he.symm).resolve_left hg
  have hfirst (i : Fin 3) (hi : i ≠ 1) :
      aeval z (pderiv 1 (H i)) = aeval z g * aeval z (pderiv 1 p) * (v i).coeff 1 := by
    rw [hfactor i, pderiv_mul]
    simp only [map_add, map_mul]
    rw [hWvalue, hc0 i hi, mul_zero, zero_add,
      homogeneous_parameter_value_first_source_derivative_at_normalized_point
        (v i) (hN i) (hc0 i hi) p q z hp hq]
    ring
  have htwo : aeval z g * aeval z (pderiv 1 p) * (v 2).coeff 1 = 1 :=
    (hfirst 2 (by decide)).symm.trans (by simpa using hder 2)
  have hpder : aeval z (pderiv 1 p) ≠ 0 := by
    intro hz
    rw [hz, mul_zero, zero_mul] at htwo
    exact zero_ne_one htwo
  have hgp : aeval z g * aeval z (pderiv 1 p) ≠ 0 := mul_ne_zero hg hpder
  have hc1 (i : Fin 3) (hi : i ≠ 1) (hi2 : i ≠ 2) : (v i).coeff 1 = 0 := by
    have he : aeval z g * aeval z (pderiv 1 p) * (v i).coeff 1 = 0 :=
      (hfirst i hi).symm.trans (by simpa only [if_neg hi2] using hder i)
    exact (mul_eq_zero.mp he).resolve_left hgp
  have hdiv (i : Fin 3) (hi : i ≠ 1) (hi2 : i ≠ 2) : g * p ^ 2 ∣ H i := by
    obtain ⟨b, hb⟩ := zero_parameter_first_jet_forces_original_source_square_divisibility
      (v i) (hN i) (hc0 i hi) (hc1 i hi hi2) p q
    refine ⟨b, ?_⟩
    rw [hfactor, hb, mul_assoc]
  exact ⟨hpder, hc0, hc1 0 (by decide) (by decide), hdiv 0 (by decide) (by decide)⟩

end DimensionFourDependence
