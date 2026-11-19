import DimensionFourDependence.TwoAxisKernelRadialOutput
import DimensionFourDependence.NilpotentBinaryOutputPair

/-! # The positive classified-direction branch of Proposition 2.1 -/

namespace DimensionFourDependence

open MvPolynomial Matrix

set_option maxHeartbeats 3500000

variable {K : Type*} [Field K] [CharZero K]
local notation "R₀" => MvPolynomial (Fin 4) K

/-- The entire nonconstant classified-direction argument of Proposition
2.1: an actual primitive positive homogeneous kernel direction
(0,0,A(x,y),B(x,y)) forces component dependence for the original map.
Both derivative cases, nonzero Wronskian, nilpotent quotient block, mixed
trace identities, Euler reduction and polynomial eigenvalue obstruction
are constructed. No invariant-ring factorization, trace pairing,
Wronskian nonvanishing or radial output identity is assumed.
Constructing the classified direction from arbitrary line fibers remains
a separate obligation. -/
theorem classified_primitive_positive_binary_kernel_direction_forces_componentsDependent
    (H : Fin 4 → R₀) {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d)
    (hN : IsNilpotent (jac H)) (A B : R₀) {e : ℕ} (he : 0 < e)
    (hA : A.IsHomogeneous e) (hB : B.IsHomogeneous e)
    (hprim : IsPrimitiveVec (![0, 0, A, B] : Fin 4 → R₀))
    (hAz : pderiv 2 A = 0) (hAw : pderiv 3 A = 0)
    (hBz : pderiv 2 B = 0) (hBw : pderiv 3 B = 0)
    (hker : jac H *ᵥ ![0, 0, A, B] = 0) : ComponentsDependent H := by
  obtain ⟨_hA0, hB0, hWr⟩ := primitive_positive_binary_direction_entries_and_wronskian_nonzero
    A B he hA hB hprim hAz hAw hBz hBw
  by_cases hvertical : ∃ i : Fin 2, pderiv 2 (H (i.castAdd 2)) ≠ 0
  · have hz := nilpotent_two_axis_kernel_nonzero_vertical_pair_zero
      H hd hH hN A B hA hB hB0 hAz hAw hBz hBw hWr hker hvertical
    exact componentsDependent_of_first_pair_relation H 1 0 (Or.inl one_ne_zero) (by simp [hz.1])
  · have hzero (i : Fin 2) : pderiv 2 (H (i.castAdd 2)) = 0 ∧ pderiv 3 (H (i.castAdd 2)) = 0 := by
      have hz : pderiv 2 (H (i.castAdd 2)) = 0 := by
        by_contra hn
        exact hvertical ⟨i, hn⟩
      have heq := congrFun hker (i.castAdd 2)
      simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, jac] at heq
      change pderiv 2 (H (i.castAdd 2)) * A + pderiv 3 (H (i.castAdd 2)) * B = 0 at heq
      rw [hz, zero_mul, zero_add] at heq
      exact ⟨hz, (mul_eq_zero.mp heq).resolve_right hB0⟩
    exact nilpotent_binary_output_pair_componentsDependent H hd hH hN hzero

end DimensionFourDependence
