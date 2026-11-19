import DimensionFourDependence.CoordinateHessianDirection
import DimensionFourDependence.SymmetrizedCubicFactor

/-! # The original Segre graph derivatives in Section 5.2 -/

namespace DimensionFourDependence

open MvPolynomial Matrix

set_option maxHeartbeats 3000000

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

/-- The graph of the determinant quadric over its first three coordinates. -/
def segreGraphFunction (Y : Fin 3 → F) : F := Y 1 * Y 2 / Y 0

variable (δ : Fin 3 → Derivation K F F) (Y : Fin 3 → F)
    (hcoord : ∀ i j, δ i (Y j) = if j = i then 1 else 0) (hY0 : Y 0 ≠ 0)

include hcoord hY0

/-- The actual first partials of the Segre graph, in the original output coordinates. -/
theorem segre_graph_gradient (i : Fin 3) :
    δ i (segreGraphFunction Y) = ![-Y 1 * Y 2 / Y 0 ^ 2, Y 2 / Y 0, Y 1 / Y 0] i := by
  fin_cases i <;>
    simp [segreGraphFunction, Derivation.leibniz_div, Derivation.leibniz, smul_eq_mul, hcoord] <;>
    field_simp <;> ring

/-- The exact Hessian retains the original radial denominator. -/
theorem segre_graph_hessian :
    derivationHessian δ (segreGraphFunction Y) =
      !![2 * Y 1 * Y 2 / Y 0 ^ 3, -Y 2 / Y 0 ^ 2, -Y 1 / Y 0 ^ 2;
        -Y 2 / Y 0 ^ 2, 0, 1 / Y 0;
        -Y 1 / Y 0 ^ 2, 1 / Y 0, 0] := by
  ext i j
  change δ i (δ j (segreGraphFunction Y)) = _
  rw [segre_graph_gradient δ Y hcoord hY0]
  fin_cases i <;> fin_cases j <;>
    simp [Derivation.leibniz_div, Derivation.leibniz, Derivation.leibniz_pow, smul_eq_mul,
      hcoord, hY0] <;> field_simp <;> ring

variable [CharZero F]

/-- The quadratic graph term is the product of the two actual transverse
coordinates, divided by the original first output. -/
theorem segre_graph_half_hessian_pairing (x : Fin 3 → F) :
    (2 : F)⁻¹ * matrixBilinearPairing (derivationHessian δ (segreGraphFunction Y)) x x =
      (x 1 - Y 1 / Y 0 * x 0) * (x 2 - Y 2 / Y 0 * x 0) / Y 0 := by
  rw [segre_graph_hessian δ Y hcoord hY0]
  simp only [matrixBilinearPairing, Fin.sum_univ_succ]
  simp
  field_simp
  ring

/-- The third graph tensor is the symmetric polarization of the
radial covector `(-3/r,0,0)` and the actual graph Hessian. -/
theorem segre_graph_cubic_polarization (i j k : Fin 3) :
    (3 : F) * derivationCubicTensor δ (segreGraphFunction Y) i j k =
      (![-3 / Y 0, 0, 0] : Fin 3 → F) i * derivationHessian δ (segreGraphFunction Y) j k +
      (![-3 / Y 0, 0, 0] : Fin 3 → F) j * derivationHessian δ (segreGraphFunction Y) i k +
      (![-3 / Y 0, 0, 0] : Fin 3 → F) k * derivationHessian δ (segreGraphFunction Y) i j := by
  have htwo : ∀ l, δ l (2 : F) = 0 := fun l => (δ l).map_natCast 2
  change 3 * δ i (derivationHessian δ (segreGraphFunction Y) j k) = _
  rw [segre_graph_hessian δ Y hcoord hY0]
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
    simp [Derivation.leibniz_div, Derivation.leibniz, Derivation.leibniz_pow, Derivation.leibniz_inv,
      htwo, smul_eq_mul,
      hcoord, hY0] <;> field_simp <;> ring

/-- The actual cubic graph polynomial has precisely the factor used
to reduce the cubic fiber equation in Section 5.2. -/
theorem segre_graph_cubic_polynomial_factorization :
    cubicFormPolynomial (derivationCubicTensor δ (segreGraphFunction Y)) =
      C (-3 / Y 0) * X 0 * quadraticFormPolynomial (derivationHessian δ (segreGraphFunction Y)) := by
  rw [cubicFormPolynomial_eq_linear_mul_quadratic_of_polarization
    (![-3 / Y 0, 0, 0] : Fin 3 → F) _ _ (segre_graph_cubic_polarization δ Y hcoord hY0)]
  simp [linearFormPolynomial, Fin.sum_univ_succ]

end DimensionFourDependence
