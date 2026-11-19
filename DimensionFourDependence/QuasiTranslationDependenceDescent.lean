import DimensionFourDependence.HomogeneousQuasiTranslationSpan
import DimensionFourDependence.ScalarExtendedMapHypotheses

/-! # The full quasi-translation dependence branch over original constants -/

namespace DimensionFourDependence

open MvPolynomial Matrix

universe u
set_option maxHeartbeats 2500000

variable {K F : Type u} [Field K] [Field F] [Algebra K F]

/-- Actual zero acceleration is preserved by the original coefficient
map, with all source variables retained. -/
theorem zero_acceleration_map_coefficients
    (H : Fin 4 → MvPolynomial (Fin 4) K) (hacc : jac H *ᵥ H = 0) :
    jac (fun i => MvPolynomial.map (algebraMap K F) (H i)) *ᵥ
      (fun i => MvPolynomial.map (algebraMap K F) (H i)) = 0 := by
  rw [jac_map_coefficients]
  funext i
  have he := congrArg (MvPolynomial.map (algebraMap K F)) (congrFun hacc i)
  simpa only [Matrix.mulVec, dotProduct, Matrix.map_apply, map_sum,
    map_mul, Pi.zero_apply, map_zero] using he

variable [CharZero K]

omit [Field F] [Algebra K F] in
/-- The entire positive homogeneous four-variable quasi-translation
case of Theorem 1.1 over every original characteristic-zero field.
The closed-field span proof is applied after actual coefficient
extension, and its constant component relation descends. -/
theorem original_field_positive_homogeneous_four_variable_quasi_translation_componentsDependent
    (H : Fin 4 → MvPolynomial (Fin 4) K) {d : ℕ} (hd : 0 < d)
    (hH : IsHomogMap H d) (hacc : jac H *ᵥ H = 0) : ComponentsDependent H := by
  apply componentsDependent_of_map (AlgebraicClosure K) H
  exact positive_homogeneous_four_variable_quasi_translation_componentsDependent
    (fun i => MvPolynomial.map (algebraMap K (AlgebraicClosure K)) (H i)) hd
    (isHomogMap_map_coefficients H hH) (zero_acceleration_map_coefficients H hacc)

omit [Field F] [Algebra K F] in
/-- The original squared-Jacobian Euler-zero case now gives
dependence over arbitrary original characteristic-zero constants. -/
theorem original_field_homogeneous_squared_jacobian_euler_zero_componentsDependent
    (H : Fin 4 → MvPolynomial (Fin 4) K) {d : ℕ} (hd : 0 < d)
    (hH : IsHomogMap H d) (hzero : jac H ^ 2 *ᵥ coordVec = 0) : ComponentsDependent H := by
  have he := hzero
  rw [pow_two, ← Matrix.mulVec_mulVec, euler_identity H hH, Matrix.mulVec_smul] at he
  have hacc : jac H *ᵥ H = 0 := (smul_eq_zero.mp he).resolve_left (by exact_mod_cast hd.ne')
  exact original_field_positive_homogeneous_four_variable_quasi_translation_componentsDependent H hd hH hacc

omit [Field F] [Algebra K F] in
/-- Every remaining independent original map has a nonzero second
Jacobian iterate on its source Euler vector. No nilpotence or rank
assumption is needed for this obstruction. -/
theorem original_independent_homogeneous_four_variable_squared_jacobian_euler_ne_zero
    (H : Fin 4 → MvPolynomial (Fin 4) K) {d : ℕ} (hd : 0 < d)
    (hH : IsHomogMap H d) (hind : ¬ComponentsDependent H) :
    jac H ^ 2 *ᵥ coordVec ≠ 0 :=
  fun hz => hind (original_field_homogeneous_squared_jacobian_euler_zero_componentsDependent H hd hH hz)

end DimensionFourDependence
