import DimensionFourDependence.TernaryHomogeneousNilpotentDependence
import DimensionFourDependence.ScalarExtendedMapHypotheses

/-! # Homogeneous ternary nilpotent dependence over every original coefficient field -/

namespace DimensionFourDependence

open Matrix MvPolynomial

universe u
set_option maxHeartbeats 3000000

variable {K F : Type u} [Field K] [Field F] [Algebra K F] {n : ℕ}

/-- The polynomial Jacobian commutes with actual coefficient
extension in every finite source dimension. -/
theorem general_jacobian_map_coefficients
    (H : Fin n → MvPolynomial (Fin n) K) :
    jac (fun i => MvPolynomial.map (algebraMap K F) (H i)) =
      (jac H).map (MvPolynomial.map (algebraMap K F)) := by
  funext i j
  exact MvPolynomial.pderiv_map (φ := algebraMap K F) (f := H i) (i := j)

/-- Actual nilpotence survives coefficient extension in every
finite source dimension. -/
theorem general_nilpotent_jacobian_map_coefficients
    (H : Fin n → MvPolynomial (Fin n) K) (hN : IsNilpotent (jac H)) :
    IsNilpotent (jac (fun i => MvPolynomial.map (algebraMap K F) (H i))) := by
  rw [general_jacobian_map_coefficients]
  exact hN.map (MvPolynomial.map (algebraMap K F)).mapMatrix

variable [CharZero K]

omit [Field F] [Algebra K F] in
/-- The complete homogeneous three-variable nilpotent dependence
theorem over every original characteristic-zero field. The actual
coefficient extension is used only to prove the closed-field case;
the resulting constant relation descends to the original field. -/
theorem original_field_positive_homogeneous_ternary_nilpotent_componentsDependent
    (H : Fin 3 → MvPolynomial (Fin 3) K) {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d)
    (hN : IsNilpotent (jac H)) : ComponentsDependent H := by
  apply componentsDependent_of_map (AlgebraicClosure K) H
  exact closed_field_positive_homogeneous_ternary_nilpotent_componentsDependent
    (fun i => MvPolynomial.map (algebraMap K (AlgebraicClosure K)) (H i)) hd
    (fun i => (hH i).map (algebraMap K (AlgebraicClosure K)))
    (general_nilpotent_jacobian_map_coefficients H hN)

end DimensionFourDependence
