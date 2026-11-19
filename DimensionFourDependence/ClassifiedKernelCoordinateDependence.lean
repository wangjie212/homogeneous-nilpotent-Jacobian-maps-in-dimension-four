import DimensionFourDependence.ClassifiedBinaryDirectionDependence
import DimensionFourDependence.PolynomialKernelConjugacy
import DimensionFourDependence.PrimitivePolynomialConjugacy

/-! # The actual primitive source kernel and the classified-direction obstruction -/

namespace DimensionFourDependence

open MvPolynomial Matrix

set_option maxHeartbeats 3500000
set_option synthInstance.maxHeartbeats 100000

variable {K : Type*} [Field K] [CharZero K]
local notation "R₀" => MvPolynomial (Fin 4) K

/-- The actual primitive right kernel of the original map may be put
in any specified inverse linear coordinates. If its positive-degree
normal form is the binary two-axis form, the original map has dependent
components. Homogeneity, primitivity, kernel transport, nilpotence and
the entire classified-direction argument are derived after the coordinate
choice. Existence of that coordinate choice is not asserted here. -/
theorem primitive_positive_kernel_in_binary_coordinates_forces_original_componentsDependent
    (H : Fin 4 → R₀) {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d)
    (hN : IsNilpotent (jac H)) (u : Fin 4 → R₀) {e : ℕ}
    (hu : IsPrimRightKernel (jac H) u e) (he : 0 < e)
    (T S : Matrix (Fin 4) (Fin 4) K) (hTS : T * S = 1) (hST : S * T = 1)
    (A B : R₀) (hform : linearPolynomialConjugate T S u = ![0, 0, A, B])
    (hAz : pderiv 2 A = 0) (hAw : pderiv 3 A = 0)
    (hBz : pderiv 2 B = 0) (hBw : pderiv 3 B = 0) : ComponentsDependent H := by
  have hH' := linearPolynomialConjugate_homogeneous T S H hH
  have hN' := linearPolynomialConjugate_nilpotent T S hTS hST H hN
  have hhom := linearPolynomialConjugate_homogeneous T S u hu.homog
  have hprim := linearPolynomialConjugate_preserves_primitive_vector T S hTS hST u hu.prim
  have hker := linearPolynomialConjugate_preserves_polynomial_right_kernel T S hTS H u hu.ker
  rw [hform] at hhom hprim hker
  have hA : A.IsHomogeneous e := hhom 2
  have hB : B.IsHomogeneous e := hhom 3
  have hdep := classified_primitive_positive_binary_kernel_direction_forces_componentsDependent
    (linearPolynomialConjugate T S H) hd hH' hN' A B he hA hB hprim hAz hAw hBz hBw hker
  by_contra hind
  exact linearPolynomialConjugate_componentsIndependent T S hTS hST H hind hdep

/-- The original homogeneous nilpotent map constructs its own nonzero
primitive homogeneous polynomial kernel. Its positive-degree classified
branch has the complete original-field dependence conclusion. The
classification and degree-zero kernel cases remain separate obligations. -/
theorem original_homogeneous_nilpotent_map_constructs_primitive_kernel_and_classified_positive_branch
    (H : Fin 4 → R₀) {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d)
    (hN : IsNilpotent (jac H)) :
    ∃ (u : Fin 4 → R₀) (e : ℕ), IsPrimRightKernel (jac H) u e ∧
      (0 < e → ∀ (T S : Matrix (Fin 4) (Fin 4) K), T * S = 1 → S * T = 1 →
        ∀ A B : R₀, linearPolynomialConjugate T S u = ![0, 0, A, B] →
          pderiv 2 A = 0 → pderiv 3 A = 0 → pderiv 2 B = 0 → pderiv 3 B = 0 →
          ComponentsDependent H) := by
  obtain ⟨u, e, hu⟩ := exists_primRightKernel (jac H) (fun i j => (hH i).pderiv (i := j))
    (by have hr := rank_at_most_three H hN; omega)
  exact ⟨u, e, hu, fun he T S hTS hST A B hform hAz hAw hBz hBw =>
    primitive_positive_kernel_in_binary_coordinates_forces_original_componentsDependent
      H hd hH hN u hu he T S hTS hST A B hform hAz hAw hBz hBw⟩

end DimensionFourDependence
