import DimensionFourDependence.RationalJacobianCriterion
import DimensionFourDependence.MatrixRankFieldMap
import DimensionFourDependence.FiberEquations

/-! # The dimension of the actual graph-gradient image

The source Jacobian of the coefficient gradient factors as the actual
coefficient Hessian times the selected-output Jacobian. The latter has
full row rank. The Jacobian criterion and preservation of matrix rank
under the coefficient-field embedding identify the gradient image dimension.
-/

namespace DimensionFourDependence

open Matrix

variable {K : Type*} [Field K] [CharZero K]

/-- The graph-gradient Jacobian is the actual coefficient Hessian
times the selected-output Jacobian, with symmetry fixing the row order. -/
theorem coefficient_gradient_jacobian_factorization
    (Y : Fin 3 → FractionRing (MvPolynomial (Fin 4) K)) (hY : AlgebraicIndependent K Y)
    (h : coefficientField (K := K) Y) :
    rationalJacobian (fiberGradient Y hY h) =
      (coefficientHessian Y hY h).map (algebraMap (coefficientField (K := K) Y)
        (FractionRing (MvPolynomial (Fin 4) K))) * rationalJacobian Y := by
  have he := coefficient_jacobian_factorization Y hY (coefficientGradient Y hY h)
  have hA : (Matrix.of fun i j => (coefficientPartial Y hY j (coefficientGradient Y hY h i) :
      FractionRing (MvPolynomial (Fin 4) K))) =
      (coefficientHessian Y hY h).map (algebraMap (coefficientField (K := K) Y)
        (FractionRing (MvPolynomial (Fin 4) K))) := by
    ext i j
    exact congrArg (fun z : coefficientField (K := K) Y => (z : FractionRing (MvPolynomial (Fin 4) K)))
      (coefficientPartials_commute Y hY j i h)
  rw [hA] at he
  exact he

/-- The source Jacobian of the actual coefficient gradient has
exactly the rank of the Hessian over its original coefficient field. -/
theorem coefficient_gradient_jacobian_rank
    (Y : Fin 3 → FractionRing (MvPolynomial (Fin 4) K)) (hY : AlgebraicIndependent K Y)
    (h : coefficientField (K := K) Y) :
    (rationalJacobian (fiberGradient Y hY h)).rank = (coefficientHessian Y hY h).rank := by
  rw [coefficient_gradient_jacobian_factorization,
    matrix_rank_mul_full_row_rank _ _ (rationalJacobian_rank_of_independent Y hY)]
  exact matrix_rank_field_map _ _

/-- The actual graph-gradient image field has transcendence degree
equal to the original coefficient Hessian rank. -/
theorem coefficient_gradient_image_trdeg
    (Y : Fin 3 → FractionRing (MvPolynomial (Fin 4) K)) (hY : AlgebraicIndependent K Y)
    (h : coefficientField (K := K) Y) :
    Algebra.trdeg K (IntermediateField.adjoin K (Set.range (fiberGradient Y hY h))) =
      (coefficientHessian Y hY h).rank := by
  rw [rationalJacobian_rank_eq_output_trdeg, coefficient_gradient_jacobian_rank]

end DimensionFourDependence
