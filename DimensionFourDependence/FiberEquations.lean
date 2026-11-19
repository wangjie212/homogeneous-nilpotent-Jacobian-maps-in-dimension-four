import DimensionFourDependence.ThirdInvariant
import DimensionFourDependence.FiberPolynomialGradients

/-! # The actual fiber equations over the coefficient field

These polynomials use independent indeterminates over `L`. Their degrees,
their vanishing at the source generic point and their polynomial gradients
are verified separately from the identities in the source function field.
-/

namespace DimensionFourDependence

open MvPolynomial Matrix

variable {K : Type*} [Field K] [CharZero K]

noncomputable def coefficientGradient
    (Y : Fin 3 → FractionRing (MvPolynomial (Fin 4) K)) (hY : AlgebraicIndependent K Y)
    (f : coefficientField (K := K) Y) : Fin 3 → coefficientField (K := K) Y :=
  fun i => coefficientPartial (K := K) Y hY i f

noncomputable def coefficientHessian
    (Y : Fin 3 → FractionRing (MvPolynomial (Fin 4) K)) (hY : AlgebraicIndependent K Y)
    (f : coefficientField (K := K) Y) : Matrix (Fin 3) (Fin 3) (coefficientField (K := K) Y) :=
  Matrix.of fun i j => coefficientPartial (K := K) Y hY i (coefficientPartial (K := K) Y hY j f)

noncomputable def coefficientCubicTensor
    (Y : Fin 3 → FractionRing (MvPolynomial (Fin 4) K)) (hY : AlgebraicIndependent K Y)
    (f : coefficientField (K := K) Y) : Fin 3 → Fin 3 → Fin 3 → coefficientField (K := K) Y :=
  fun i j k => coefficientPartial (K := K) Y hY i (coefficientPartial (K := K) Y hY j
    (coefficientPartial (K := K) Y hY k f))

theorem coefficientHessian_symmetric
    (Y : Fin 3 → FractionRing (MvPolynomial (Fin 4) K)) (hY : AlgebraicIndependent K Y)
    (f : coefficientField (K := K) Y) (i j : Fin 3) :
    coefficientHessian Y hY f i j = coefficientHessian Y hY f j i :=
  coefficientPartials_commute Y hY i j f

theorem coefficientCubicTensor_swap12
    (Y : Fin 3 → FractionRing (MvPolynomial (Fin 4) K)) (hY : AlgebraicIndependent K Y)
    (f : coefficientField (K := K) Y) (i j k : Fin 3) :
    coefficientCubicTensor Y hY f i j k = coefficientCubicTensor Y hY f j i k :=
  coefficientPartials_commute Y hY i j (coefficientPartial (K := K) Y hY k f)

theorem coefficientCubicTensor_swap23
    (Y : Fin 3 → FractionRing (MvPolynomial (Fin 4) K)) (hY : AlgebraicIndependent K Y)
    (f : coefficientField (K := K) Y) (i j k : Fin 3) :
    coefficientCubicTensor Y hY f i j k = coefficientCubicTensor Y hY f i k j :=
  congrArg (coefficientPartial (K := K) Y hY i) (coefficientPartials_commute Y hY j k f)

/-- The hyperplane equation as a polynomial over the actual field `L`. -/
noncomputable def affineFiberEquation
    (Y : Fin 3 → FractionRing (MvPolynomial (Fin 4) K)) (hY : AlgebraicIndependent K Y)
    (h c : coefficientField (K := K) Y) : MvPolynomial (Fin 4) (coefficientField (K := K) Y) :=
  affineFiberPolynomial (coefficientGradient Y hY h) c

/-- The quadratic equation over `L` in the first three reordered source variables. -/
noncomputable def quadraticFiberEquation
    (Y : Fin 3 → FractionRing (MvPolynomial (Fin 4) K)) (hY : AlgebraicIndependent K Y)
    (h c q : coefficientField (K := K) Y) : MvPolynomial (Fin 3) (coefficientField (K := K) Y) :=
  quadraticFiberPolynomial (coefficientGradient Y hY c) (coefficientHessian Y hY h) q

/-- The cubic equation over `L` in the same three indeterminates. -/
noncomputable def cubicFiberEquation
    (Y : Fin 3 → FractionRing (MvPolynomial (Fin 4) K)) (hY : AlgebraicIndependent K Y)
    (h c q k : coefficientField (K := K) Y) : MvPolynomial (Fin 3) (coefficientField (K := K) Y) :=
  cubicFiberPolynomial (coefficientGradient Y hY q) (coefficientHessian Y hY c)
    (coefficientCubicTensor Y hY h) k

theorem affineFiberEquation_totalDegree
    (Y : Fin 3 → FractionRing (MvPolynomial (Fin 4) K)) (hY : AlgebraicIndependent K Y)
    (h c : coefficientField (K := K) Y) : (affineFiberEquation Y hY h c).totalDegree ≤ 1 :=
  affineFiberPolynomial_totalDegree _ _

theorem affineFiberEquation_pderiv_last
    (Y : Fin 3 → FractionRing (MvPolynomial (Fin 4) K)) (hY : AlgebraicIndependent K Y)
    (h c : coefficientField (K := K) Y) : pderiv (Fin.last 3) (affineFiberEquation Y hY h c) = 1 :=
  affineFiberPolynomial_pderiv_last _ _

theorem quadraticFiberEquation_totalDegree
    (Y : Fin 3 → FractionRing (MvPolynomial (Fin 4) K)) (hY : AlgebraicIndependent K Y)
    (h c q : coefficientField (K := K) Y) : (quadraticFiberEquation Y hY h c q).totalDegree ≤ 2 :=
  quadraticFiberPolynomial_totalDegree _ _ _

theorem cubicFiberEquation_totalDegree
    (Y : Fin 3 → FractionRing (MvPolynomial (Fin 4) K)) (hY : AlgebraicIndependent K Y)
    (h c q k : coefficientField (K := K) Y) : (cubicFiberEquation Y hY h c q k).totalDegree ≤ 3 :=
  cubicFiberPolynomial_totalDegree _ _ _ _

theorem affineFiberEquation_aeval_zero (p : Equiv.Perm (Fin 4))
    (Y : Fin 3 → FractionRing (MvPolynomial (Fin 4) K)) (hY : AlgebraicIndependent K Y)
    (h c : coefficientField (K := K) Y)
    (hc : (c : FractionRing (MvPolynomial (Fin 4) K)) = firstFiberInvariantInChart p Y hY h) :
    aeval (fun i => rationalCoordinate (K := K) (p i)) (affineFiberEquation Y hY h c) = 0 := by
  rw [affineFiberEquation, affineFiberPolynomial_aeval]
  simp only [coefficientGradient, IntermediateField.algebraMap_apply]
  change firstFiberInvariantInChart p Y hY h - (c : FractionRing (MvPolynomial (Fin 4) K)) = 0
  exact sub_eq_zero.mpr hc.symm

theorem quadraticFiberEquation_aeval_zero (p : Equiv.Perm (Fin 4))
    (Y : Fin 3 → FractionRing (MvPolynomial (Fin 4) K)) (hY : AlgebraicIndependent K Y)
    (h c q : coefficientField (K := K) Y)
    (hq : (q : FractionRing (MvPolynomial (Fin 4) K)) = secondFiberInvariant p Y hY h c) :
    aeval (fun i => rationalCoordinate (K := K) (p i.castSucc)) (quadraticFiberEquation Y hY h c q) = 0 := by
  rw [quadraticFiberEquation, quadraticFiberPolynomial_aeval]
  simp only [coefficientGradient, coefficientHessian, Matrix.of_apply, IntermediateField.algebraMap_apply]
  change secondFiberInvariant p Y hY h c - (q : FractionRing (MvPolynomial (Fin 4) K)) = 0
  exact sub_eq_zero.mpr hq.symm

theorem cubicFiberEquation_aeval_zero (p : Equiv.Perm (Fin 4))
    (Y : Fin 3 → FractionRing (MvPolynomial (Fin 4) K)) (hY : AlgebraicIndependent K Y)
    (h c q k : coefficientField (K := K) Y)
    (hk : (k : FractionRing (MvPolynomial (Fin 4) K)) = thirdFiberInvariant p Y hY h c q) :
    aeval (fun i => rationalCoordinate (K := K) (p i.castSucc)) (cubicFiberEquation Y hY h c q k) = 0 := by
  rw [cubicFiberEquation, cubicFiberPolynomial_aeval]
  simp only [coefficientGradient, coefficientHessian, coefficientCubicTensor,
    Matrix.of_apply, IntermediateField.algebraMap_apply]
  change thirdFiberInvariant p Y hY h c q - (k : FractionRing (MvPolynomial (Fin 4) K)) = 0
  exact sub_eq_zero.mpr hk.symm

theorem quadraticFiberEquation_gradient_aeval (p : Equiv.Perm (Fin 4))
    (Y : Fin 3 → FractionRing (MvPolynomial (Fin 4) K)) (hY : AlgebraicIndependent K Y)
    (h c q : coefficientField (K := K) Y) (i : Fin 3) :
    aeval (fun j => rationalCoordinate (K := K) (p j.castSucc))
      (pderiv i (quadraticFiberEquation Y hY h c q)) = fiberSecondCovector p Y hY h c i := by
  have hd := quadraticFiberPolynomial_gradient_aeval (coefficientGradient Y hY c)
    (coefficientHessian Y hY h) q (coefficientHessian_symmetric Y hY h)
    (fun j => rationalCoordinate (K := K) (p j.castSucc)) i
  simpa only [quadraticFiberEquation, coefficientGradient, coefficientHessian, Matrix.of_apply,
    IntermediateField.algebraMap_apply, fiberSecondCovector, fiberHessian] using hd

theorem cubicFiberEquation_gradient_aeval (p : Equiv.Perm (Fin 4))
    (Y : Fin 3 → FractionRing (MvPolynomial (Fin 4) K)) (hY : AlgebraicIndependent K Y)
    (h c q k : coefficientField (K := K) Y) (i : Fin 3) :
    aeval (fun j => rationalCoordinate (K := K) (p j.castSucc))
      (pderiv i (cubicFiberEquation Y hY h c q k)) = fiberThirdCovector p Y hY h c q i := by
  have hd := cubicFiberPolynomial_gradient_aeval (coefficientGradient Y hY q)
    (coefficientHessian Y hY c) (coefficientCubicTensor Y hY h) k
    (coefficientHessian_symmetric Y hY c) (coefficientCubicTensor_swap12 Y hY h)
    (coefficientCubicTensor_swap23 Y hY h) (fun j => rationalCoordinate (K := K) (p j.castSucc)) i
  simpa only [cubicFiberEquation, coefficientGradient, coefficientHessian, coefficientCubicTensor,
    Matrix.of_apply, IntermediateField.algebraMap_apply, fiberThirdCovector, fiberHessian,
    fiberThirdDerivative] using hd

end DimensionFourDependence
