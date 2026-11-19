import DimensionFourDependence.SegreFiberCoordinates
import DimensionFourDependence.StandardRulingQuadric

/-! # Section 5.4: exact zero-pairing quadratic and affine cubic equations -/

namespace DimensionFourDependence

open MvPolynomial Matrix

set_option maxHeartbeats 3000000

variable {K E F : Type*} [Field K] [Field E] [Algebra K E]
    [CharZero E] [Field F] [Algebra E F]

/-- The actual third-equation coefficient vector when c=0. -/
def segreZeroPairingThirdCovector (δ : Fin 3 → Derivation K E E) (Y : Fin 3 → E) (q : E) : Fin 3 → E :=
  fun i => δ i q + if i = 0 then q / Y 0 else 0

/-- The zero-gradient quadratic expression is precisely the product
of the two original transverse source coordinates divided by the radial output. -/
theorem segre_zero_gradient_quadratic_expression
    (δ : Fin 3 → Derivation K E E) (Y : Fin 3 → E)
    (hcoord : ∀ i j, δ i (Y j) = if j = i then 1 else 0) (hY0 : Y 0 ≠ 0)
    (x : Fin 3 → F) :
    quadraticExpression 0 ((derivationHessian δ (segreGraphFunction Y)).map (algebraMap E F)) x =
      (x 1 - algebraMap E F (Y 1) / algebraMap E F (Y 0) * x 0) *
        (x 2 - algebraMap E F (Y 2) / algebraMap E F (Y 0) * x 0) / algebraMap E F (Y 0) := by
  simpa only [quadraticExpression, Pi.zero_apply, zero_mul, Finset.sum_const_zero,
    zero_add, matrixBilinearPairing] using
      segre_graph_half_hessian_pairing_base_change δ Y hcoord hY0 x

/-- The exact original quadratic polynomial equation gives the
nonzero-pairing branch's replacement q=vw/r, with no auxiliary q formula. -/
theorem segre_zero_pairing_quadratic_equation_value
    (δ : Fin 3 → Derivation K E E) (Y : Fin 3 → E)
    (hcoord : ∀ i j, δ i (Y j) = if j = i then 1 else 0) (hY0 : Y 0 ≠ 0)
    (x : Fin 3 → F) (q : E)
    (hQ : aeval x (quadraticFiberPolynomial 0 (derivationHessian δ (segreGraphFunction Y)) q) = 0) :
    algebraMap E F q =
      (x 1 - algebraMap E F (Y 1) / algebraMap E F (Y 0) * x 0) *
        (x 2 - algebraMap E F (Y 2) / algebraMap E F (Y 0) * x 0) / algebraMap E F (Y 0) := by
  rw [quadraticFiberPolynomial_aeval] at hQ
  have hzero : (fun i : Fin 3 => algebraMap E F ((0 : Fin 3 → E) i)) = (0 : Fin 3 → F) := by
    funext i
    simp
  have hmatrix : (Matrix.of fun i j => algebraMap E F (derivationHessian δ (segreGraphFunction Y) i j)) =
      (derivationHessian δ (segreGraphFunction Y)).map (algebraMap E F) := by
    ext i j
    rfl
  rw [hzero, hmatrix] at hQ
  have he : algebraMap E F q =
      quadraticExpression 0 ((derivationHessian δ (segreGraphFunction Y)).map (algebraMap E F)) x := by
    exact (sub_eq_zero.mp hQ).symm
  rw [he, segre_zero_gradient_quadratic_expression δ Y hcoord hY0]

/-- The original zero-pairing quadratic and cubic equations reduce
to the actual affine third equation k=dq(x)+(q/r)x0. -/
theorem segre_zero_pairing_cubic_equation_is_affine
    (δ : Fin 3 → Derivation K E E) (Y : Fin 3 → E)
    (hcoord : ∀ i j, δ i (Y j) = if j = i then 1 else 0) (hY0 : Y 0 ≠ 0)
    (x : Fin 3 → F) (q k : E)
    (hQ : aeval x (quadraticFiberPolynomial 0 (derivationHessian δ (segreGraphFunction Y)) q) = 0)
    (hC : aeval x (cubicFiberPolynomial (fun i => δ i q) 0
      (derivationCubicTensor δ (segreGraphFunction Y)) k) = 0) :
    algebraMap E F k = (fun i => algebraMap E F (segreZeroPairingThirdCovector δ Y q i)) ⬝ᵥ x := by
  let A : Fin 3 → E := ![-3 / Y 0, 0, 0]
  have hfactor : cubicFormPolynomial (derivationCubicTensor δ (segreGraphFunction Y)) =
      linearFormPolynomial A * quadraticFormPolynomial (derivationHessian δ (segreGraphFunction Y)) :=
    cubicFormPolynomial_eq_linear_mul_quadratic_of_polarization A _ _
      (segre_graph_cubic_polarization δ Y hcoord hY0)
  have hM : aeval x (modifiedCubicFiberPolynomial 0 (fun i => δ i q) A 0 q k) = 0 := by
    rw [modifiedCubicFiberPolynomial_elimination_identity _ _ _ _ _ _ _ _ hfactor]
    simp only [map_add, map_mul, hQ, hC, mul_zero, zero_add]
  letI : CharZero F := charZero_of_injective_algebraMap (algebraMap E F).injective
  have hr : algebraMap E F (Y 0) ≠ 0 := (map_ne_zero (algebraMap E F)).mpr hY0
  simp [modifiedCubicFiberPolynomial, linearFormPolynomial, quadraticFormPolynomial,
    A, Fin.sum_univ_succ, map_div₀, map_ofNat] at hM
  simp [segreZeroPairingThirdCovector, dotProduct, Fin.sum_univ_succ, map_div₀]
  field_simp [hr] at hM ⊢
  linear_combination -(6 : F)⁻¹ * hM

/-- The original graph hyperplane and quadratic equation identify
the radial second-invariant product with the negative source determinant. -/
theorem segre_zero_pairing_second_invariant_radial_product_is_negative_determinant
    (Y : Fin 3 → E) (hY0 : Y 0 ≠ 0) (x : Fin 4 → F) (q : E)
    (hgraph : x 3 = algebraMap E F (-Y 1 * Y 2 / Y 0 ^ 2) * x 0 +
      algebraMap E F (Y 2 / Y 0) * x 1 + algebraMap E F (Y 1 / Y 0) * x 2)
    (hquad : algebraMap E F q =
      (x 1 - algebraMap E F (Y 1) / algebraMap E F (Y 0) * x 0) *
        (x 2 - algebraMap E F (Y 2) / algebraMap E F (Y 0) * x 0) / algebraMap E F (Y 0)) :
    algebraMap E F (Y 0 * q) = -(x 0 * x 3 - x 1 * x 2) := by
  have hr : algebraMap E F (Y 0) ≠ 0 := (map_ne_zero (algebraMap E F)).mpr hY0
  rw [map_mul, hquad, hgraph]
  simp only [map_div₀, map_neg, map_mul, map_pow]
  field_simp [hr]
  ring

end DimensionFourDependence
