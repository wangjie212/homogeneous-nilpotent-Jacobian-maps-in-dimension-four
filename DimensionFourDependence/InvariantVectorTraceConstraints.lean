import DimensionFourDependence.Laplacian

/-! # Original nilpotent Jacobians and invariant polynomial directions give two trace constraints -/

namespace DimensionFourDependence

open MvPolynomial Matrix

set_option maxHeartbeats 2500000

variable {K R : Type*} [Field K] [CommRing R] [Algebra K R] {n : ℕ}

theorem derivation_matrix_trace (D : Derivation K R R) (M : Matrix (Fin n) (Fin n) R) :
    D (Matrix.trace M) = Matrix.trace (Matrix.of fun i j => D (M i j)) := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.of_apply, map_sum]

/-- Differentiating the second nilpotent trace retains the mixed matrix
product with its exact factor two. -/
theorem derivation_matrix_trace_square (D : Derivation K R R) (M : Matrix (Fin n) (Fin n) R) :
    D (Matrix.trace (M ^ 2)) = 2 * Matrix.trace (M * (Matrix.of fun i j => D (M i j))) := by
  simp only [pow_two, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
    Matrix.of_apply, map_sum, D.leibniz, smul_eq_mul, Finset.sum_add_distrib]
  have he : (∑ i : Fin n, ∑ j : Fin n, M j i * D (M i j)) =
      ∑ i : Fin n, ∑ j : Fin n, M i j * D (M j i) := by
    rw [Finset.sum_comm]
  rw [he]
  ring

/-- The two original nilpotent traces and the actual derivative
transport equation construct the two mixed trace constraints. -/
theorem nilpotent_derivative_transport_constructs_two_trace_constraints
    [IsDomain R] [CharZero R] (D : Derivation K R R)
    (M A : Matrix (Fin n) (Fin n) R) (hN : IsNilpotent M)
    (hD : ∀ i j, D (M i j) = -(M * A) i j) :
    Matrix.trace (M * A) = 0 ∧ Matrix.trace (M ^ 2 * A) = 0 := by
  have hmat : (Matrix.of fun i j => D (M i j)) = -(M * A) := by
    ext i j
    exact hD i j
  have htrace : Matrix.trace M = 0 := (Matrix.isNilpotent_trace_of_isNilpotent hN).eq_zero
  have htrace2 : Matrix.trace (M ^ 2) = 0 :=
    (Matrix.isNilpotent_trace_of_isNilpotent (hN.pow_of_pos (by decide : (2 : ℕ) ≠ 0))).eq_zero
  have hfirst := congrArg D htrace
  rw [derivation_matrix_trace, hmat, Matrix.trace_neg, map_zero] at hfirst
  have hsecond := congrArg D htrace2
  rw [derivation_matrix_trace_square, hmat, Matrix.mul_neg, Matrix.trace_neg, map_zero] at hsecond
  have htwo : (2 : R) ≠ 0 := by norm_num
  have hsecond0 := neg_eq_zero.mp ((mul_eq_zero.mp hsecond).resolve_left htwo)
  exact ⟨neg_eq_zero.mp hfirst, by simpa only [pow_two, Matrix.mul_assoc] using hsecond0⟩

variable {K : Type*} [Field K] {n : ℕ}
local notation "P₀" => MvPolynomial (Fin n) K

/-- The polynomial directional derivation with its original polynomial coefficients. -/
noncomputable def polynomialVectorDerivation (u : Fin n → P₀) : Derivation K P₀ P₀ :=
  ∑ i, u i • pderiv i

theorem polynomialVectorDerivation_apply (u : Fin n → P₀) (p : P₀) :
    polynomialVectorDerivation u p = ∑ i, u i * pderiv i p := by
  simp only [polynomialVectorDerivation, _root_.sum_apply, Derivation.smul_apply, smul_eq_mul]

/-- A right Jacobian kernel gives the actual invariant equations for
the same polynomial directional derivation. -/
theorem polynomialVectorDerivation_output_zero_of_kernel
    (H u : Fin n → P₀) (hker : jac H *ᵥ u = 0) (i : Fin n) :
    polynomialVectorDerivation u (H i) = 0 := by
  have he := congrFun hker i
  simpa only [polynomialVectorDerivation_apply, Matrix.mulVec, dotProduct,
    jac, Matrix.of_apply, Pi.zero_apply, mul_comm] using he

/-- Differentiating the original invariant equations supplies the entire
Jacobian transport equation, with no substituted nilpotence hypothesis. -/
theorem invariant_polynomial_direction_jacobian_derivative_transport
    (H u : Fin n → P₀) (hker : jac H *ᵥ u = 0) (i j : Fin n) :
    polynomialVectorDerivation u (jac H i j) = -(jac H * jac u) i j := by
  have he := congrArg (pderiv j) (polynomialVectorDerivation_output_zero_of_kernel H u hker i)
  simp only [polynomialVectorDerivation_apply, map_sum, pderiv_mul, map_zero,
    Finset.sum_add_distrib] at he
  change (∑ k, pderiv j (u k) * pderiv k (H i)) +
    (∑ k, u k * pderiv j (pderiv k (H i))) = 0 at he
  have hcomm (k : Fin n) : pderiv j (pderiv k (H i)) = pderiv k (pderiv j (H i)) :=
    pderiv_pderiv_comm j k (H i)
  simp only [hcomm] at he
  simpa only [polynomialVectorDerivation_apply, Matrix.mul_apply, jac,
    Matrix.of_apply, mul_comm] using eq_neg_of_add_eq_zero_right he

/-- The two mixed traces used after the quasi-translation classification
in Proposition 2.1 follow from the original nilpotent Jacobian and its
original polynomial right-kernel direction. -/
theorem invariant_polynomial_direction_constructs_two_nilpotent_trace_constraints
    [CharZero K] (H u : Fin n → P₀) (hN : IsNilpotent (jac H)) (hker : jac H *ᵥ u = 0) :
    Matrix.trace (jac H * jac u) = 0 ∧ Matrix.trace (jac H ^ 2 * jac u) = 0 :=
  nilpotent_derivative_transport_constructs_two_trace_constraints
    (polynomialVectorDerivation u) (jac H) (jac u) hN
    (invariant_polynomial_direction_jacobian_derivative_transport H u hker)

end DimensionFourDependence
