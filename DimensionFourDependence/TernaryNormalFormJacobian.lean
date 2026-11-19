import DimensionFourDependence.HomogenizedTernaryNormalForm

/-! # The actual affine canonical normal form has cube-zero Jacobian -/

namespace DimensionFourDependence.TernaryNormalForm

open Matrix MvPolynomial

set_option maxHeartbeats 2500000

/-- The displayed Jacobian in Proposition 6.6 has cube zero for
any values of the three entries `x`, `e` and `v`. -/
theorem canonical_jacobian_matrix_cube_zero {R : Type*} [CommRing R] (x e v : R) :
    (of ![![2*x*v, v, 0], ![-2*e-4*x^2*v, -2*x*v, 1], ![4*x*e*v, 2*e*v, 0]] :
      Matrix (Fin 3) (Fin 3) R) ^ 3 = 0 := by
  rw [pow_three]
  ext i j
  rw [Matrix.mul_apply]
  simp_rw [Matrix.mul_apply]
  fin_cases i <;> fin_cases j <;> simp [Fin.sum_univ_three] <;> ring

variable {K : Type*} [Field K]
local notation "R₃" => MvPolynomial (Fin 3) K

/-- Every entry of the affine canonical Jacobian agrees with the
displayed derivative matrix, by the univariate polynomial chain rule. -/
theorem jac_perturbation3_formula (P : Polynomial K) :
    let x : R₃ := X 0
    let e := Polynomial.aeval (X 1 + x ^ 2) P
    let v := Polynomial.aeval (X 1 + x ^ 2) P.derivative
    jac (perturbation3 P) = of ![![2*x*v, v, 0], ![-2*e-4*x^2*v, -2*x*v, 1],
      ![4*x*e*v, 2*e*v, 0]] := by
  dsimp only
  have hchain (i : Fin 3) : pderiv i (Polynomial.aeval (X 1 + (X 0 : R₃) ^ 2) P) =
      Polynomial.aeval (X 1 + X 0 ^ 2 : R₃) P.derivative * pderiv i (X 1 + X 0 ^ 2) := by
    simpa only [smul_eq_mul, mul_comm] using (pderiv (R := K) i).map_aeval P (X 1 + X 0 ^ 2)
  have h₂ (i : Fin 3) : pderiv i (2 : R₃) = 0 := by
    rw [show (2 : R₃) = C (2 : K) by simp [map_ofNat], pderiv_C]
  funext i j
  fin_cases i <;> fin_cases j <;>
    simp [jac, perturbation3, hchain, h₂, pderiv_mul, pderiv_pow, pderiv_X, Pi.single_apply] <;> ring

theorem jac_perturbation3_cube_zero (P : Polynomial K) : jac (perturbation3 P) ^ 3 = 0 := by
  rw [jac_perturbation3_formula]
  exact canonical_jacobian_matrix_cube_zero _ _ _

end DimensionFourDependence.TernaryNormalForm
