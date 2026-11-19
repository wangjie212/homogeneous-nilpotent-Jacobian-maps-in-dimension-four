import DimensionFourDependence.RulingDirectionAcceleration
import DimensionFourDependence.SimpleFixedRootHessian

/-! # Mixed derivatives on the actual graph ruling

Constant parameter-defined directions identify mixed coordinate
derivatives with the original Hessian pairing. Differentiating the
actual ruling denominator gives the mixed product formula for nc.
The root equation then gives the nonzero mixed derivative at the
fixed simple root.
-/

namespace DimensionFourDependence

open Matrix

variable {K F : Type*} [Field K] [Field F] [Algebra K F] {n : ℕ}

/-- A direction constant for the outer directional derivation gives
exactly the original ordered mixed Hessian pairing. -/
theorem coordinate_direction_mixed_derivative
    (delta : Fin n → Derivation K F F) (v w : Fin n → F)
    (hw : ∀ i, coordinateEuler v delta (w i) = 0) (c : F) :
    coordinateEuler v delta (coordinateEuler w delta c) =
      matrixBilinearPairing (derivationHessian delta c) v w := by
  rw [coordinateEuler_apply w delta c, map_sum]
  simp only [Derivation.leibniz, hw, smul_eq_mul, mul_zero, add_zero,
    coordinateEuler_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  simp only [matrixBilinearPairing, derivationHessian, Matrix.of_apply]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- The full mixed product derivative retains all four product terms. -/
theorem derivation_mixed_product (D E : Derivation K F F) (a b : F) :
    D (E (a * b)) = D (E a) * b + E a * D b + D a * E b + a * D (E b) := by
  rw [E.leibniz, map_add]
  simp only [smul_eq_mul, D.leibniz]
  ring

section Root

variable [CharZero F]

/-- The fixed-root coordinate direction has first derivative rho,
zero second derivative, and nonzero transverse mixed derivative.
Every derivative of rho follows from rho^d=s. -/
theorem linear_root_factor_fixed_and_mixed_derivatives
    (D E : Derivation K F F) {d : ℕ} (hd : 0 < d)
    (r s rho : F) (hrho : rho ≠ 0) (hroot : rho ^ d = s)
    (hr : D r = 1) (hs : D s = 0) (hEs : E s = 1) :
    D (r * rho) = rho ∧ D (D (r * rho)) = 0 ∧
      E (D (r * rho)) = (d : F)⁻¹ * rho / s ∧ E (D (r * rho)) ≠ 0 := by
  have hD : D rho = 0 := by
    rw [linear_coordinate_root_derivative D hd rho s hrho hroot, hs, mul_zero]
  have hfirst : D (r * rho) = rho := by
    rw [D.leibniz, hr, hD]
    simp only [smul_eq_mul, mul_zero, zero_add, mul_one]
  have hE : E rho = (d : F)⁻¹ * rho / s := by
    rw [linear_coordinate_root_derivative E hd rho s hrho hroot, hEs, mul_one]
  refine ⟨hfirst, by rw [hfirst, hD], by rw [hfirst, hE], ?_⟩
  rw [hfirst, hE]
  exact div_ne_zero (mul_ne_zero (inv_ne_zero (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hd))) hrho)
    (hroot ▸ pow_ne_zero d hrho)

end Root

section Parameter

variable [CharZero K]

/-- The actual parameter equation and algebraic ruling directions
construct the full mixed second derivative of nc, including both
denominator-gradient cross terms. -/
theorem parametric_ruling_mixed_product_derivative
    (p : RatFunc K →ₐ[K] F) (delta : Fin n → Derivation K F F) (y : Fin n → F)
    (hcoord : ∀ i j, delta i (y j) = if j = i then 1 else 0)
    (A : Fin n → RatFunc K)
    (htangent : (fun i => p (rationalParameterDerivative K (A i))) ⬝ᵥ y = 0)
    (hfirst : (fun i => p (rationalParameterDerivative K (A i))) ≠ 0)
    (v w : Fin n → F)
    (hv : (fun i => p (rationalParameterDerivative K (A i))) ⬝ᵥ v = 0)
    (hw : (fun i => p (rationalParameterDerivative K (A i))) ⬝ᵥ w = 0)
    (halgw : ∀ i, IsAlgebraic p.fieldRange (w i)) (c : F) :
    coordinateEuler v delta (coordinateEuler w delta (parametricRulingDenominator p A y * c)) =
      parametricRulingDenominator p A y * matrixBilinearPairing (derivationHessian delta c) v w +
        ((fun i => p (rationalParameterDerivative K (rationalParameterDerivative K (A i)))) ⬝ᵥ v) *
          ((fun i => delta i c) ⬝ᵥ w) +
        ((fun i => p (rationalParameterDerivative K (rationalParameterDerivative K (A i)))) ⬝ᵥ w) *
          ((fun i => delta i c) ⬝ᵥ v) := by
  let D := coordinateEuler v delta
  let E := coordinateEuler w delta
  let N := parametricRulingDenominator p A y
  have ht : D (p RatFunc.X) = 0 :=
    parametric_ruling_direction_fixes_parameter p delta y hcoord A htangent hfirst v hv
  have hzero (r : RatFunc K) : D (p r) = 0 := by
    rw [rational_parameter_chain_rule p D r, ht, mul_zero]
  have hwD (i : Fin n) : D (w i) = 0 :=
    parameter_algebraic_coefficient_direction_constant p D ht (w i) (halgw i)
  have hDN : D N = (fun i => p (rationalParameterDerivative K (rationalParameterDerivative K (A i)))) ⬝ᵥ v :=
    parametric_ruling_direction_denominator_derivative p delta y hcoord A htangent hfirst v hv
  have hEN : E N = (fun i => p (rationalParameterDerivative K (rationalParameterDerivative K (A i)))) ⬝ᵥ w :=
    parametric_ruling_direction_denominator_derivative p delta y hcoord A htangent hfirst w hw
  have hDEN : D (E N) = 0 := by
    rw [hEN, derivation_dotProduct]
    simp [dotProduct, hzero, hwD]
  have hDc : D c = (fun i => delta i c) ⬝ᵥ v := coordinate_direction_apply_eq_gradient_pairing delta v c
  have hEc : E c = (fun i => delta i c) ⬝ᵥ w := coordinate_direction_apply_eq_gradient_pairing delta w c
  have hDEc : D (E c) = matrixBilinearPairing (derivationHessian delta c) v w :=
    coordinate_direction_mixed_derivative delta v w hwD c
  change D (E (N * c)) = _
  rw [derivation_mixed_product, hDEN, hDN, hEN, hDEc, hDc, hEc]
  ring

end Parameter

end DimensionFourDependence
