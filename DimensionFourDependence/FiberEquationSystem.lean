import DimensionFourDependence.FiberEquations

/-! # The checked polynomial-equation input to the geometry of Lemma 2.2

The witness records genuine polynomials over the actual coefficient field,
their degree bounds, vanishing at the source generic point, and independence
of the two gradients. It does not assert a geometric degree bound.
-/

namespace DimensionFourDependence

open MvPolynomial Matrix

variable {K : Type*} [Field K] [CharZero K]

/-- The three equations and the generic transversality data supplied by
the algebraic part of Lemma 2.2. -/
structure FiberEquationWitness (H : Fin 4 → FractionRing (MvPolynomial (Fin 4) K)) where
  chart : Equiv.Perm (Fin 4)
  independent : AlgebraicIndependent K (fun i : Fin 3 => H (chart i.castSucc))
  hyperplane : MvPolynomial (Fin 4) (coefficientField (K := K) (fun i : Fin 3 => H (chart i.castSucc)))
  quadric : MvPolynomial (Fin 3) (coefficientField (K := K) (fun i : Fin 3 => H (chart i.castSucc)))
  cubic : MvPolynomial (Fin 3) (coefficientField (K := K) (fun i : Fin 3 => H (chart i.castSucc)))
  hyperplane_degree : hyperplane.totalDegree ≤ 1
  hyperplane_last_derivative : pderiv (Fin.last 3) hyperplane = 1
  quadric_degree : quadric.totalDegree ≤ 2
  cubic_degree : cubic.totalDegree ≤ 3
  hyperplane_zero : aeval (fun i => rationalCoordinate (K := K) (chart i)) hyperplane = 0
  quadric_zero : aeval (fun i => rationalCoordinate (K := K) (chart i.castSucc)) quadric = 0
  cubic_zero : aeval (fun i => rationalCoordinate (K := K) (chart i.castSucc)) cubic = 0
  gradients_independent : ∀ s t : FractionRing (MvPolynomial (Fin 4) K),
    s • (fun i => aeval (fun j => rationalCoordinate (K := K) (chart j.castSucc)) (pderiv i cubic)) +
      t • (fun i => aeval (fun j => rationalCoordinate (K := K) (chart j.castSucc)) (pderiv i quadric)) = 0 →
        s = 0 ∧ t = 0

/-- Every nilpotent rank-three rational map supplies the polynomial
equations and gradient independence used at the end of Lemma 2.2. -/
theorem exists_fiber_equation_witness
    (H : Fin 4 → FractionRing (MvPolynomial (Fin 4) K))
    (hN : IsNilpotent (rationalJacobian H)) (hrank : (rationalJacobian H).rank = 3) :
    Nonempty (FiberEquationWitness H) := by
  obtain ⟨p, hY, h, c, q, k, hh, hc, hq, hk⟩ := exists_three_fiber_invariants H hN hrank
  let Y : Fin 3 → FractionRing (MvPolynomial (Fin 4) K) := fun i => H (p i.castSucc)
  let x : Fin 3 → FractionRing (MvPolynomial (Fin 4) K) :=
    fun i => rationalCoordinate (K := K) (p i.castSucc)
  let P := quadraticFiberEquation Y hY h c q
  let S := cubicFiberEquation Y hY h c q k
  have hA : (fun i => aeval x (pderiv i S)) = fiberThirdCovector p Y hY h c q := by
    funext i
    exact cubicFiberEquation_gradient_aeval p Y hY h c q k i
  have hB : (fun i => aeval x (pderiv i P)) = fiberSecondCovector p Y hY h c := by
    funext i
    exact quadraticFiberEquation_gradient_aeval p Y hY h c q i
  refine ⟨{
    chart := p
    independent := hY
    hyperplane := affineFiberEquation Y hY h c
    quadric := P
    cubic := S
    hyperplane_degree := affineFiberEquation_totalDegree Y hY h c
    hyperplane_last_derivative := affineFiberEquation_pderiv_last Y hY h c
    quadric_degree := quadraticFiberEquation_totalDegree Y hY h c q
    cubic_degree := cubicFiberEquation_totalDegree Y hY h c q k
    hyperplane_zero := affineFiberEquation_aeval_zero p Y hY h c hc
    quadric_zero := quadraticFiberEquation_aeval_zero p Y hY h c q hq
    cubic_zero := cubicFiberEquation_aeval_zero p Y hY h c q k hk
    gradients_independent := ?_ }⟩
  intro s t hrel
  apply fiber_covectors_independent H p hY h c q hh hc hq s t
  change s • (fun i => aeval x (pderiv i S)) + t • (fun i => aeval x (pderiv i P)) = 0 at hrel
  rwa [hA, hB] at hrel

/-- The polynomial equations, degrees and independent gradients follow
from the original polynomial nilpotent-Jacobian rank-three hypotheses. -/
theorem exists_fiber_equation_witness_polynomial
    (H : Fin 4 → MvPolynomial (Fin 4) K) (hN : IsNilpotent (jac H))
    (hrank : polyRank (jac H) = 3) :
    Nonempty (FiberEquationWitness (fun i => algebraMap (MvPolynomial (Fin 4) K)
      (FractionRing (MvPolynomial (Fin 4) K)) (H i))) := by
  let Q : Fin 4 → FractionRing (MvPolynomial (Fin 4) K) :=
    fun i => algebraMap (MvPolynomial (Fin 4) K) _ (H i)
  have hJ : rationalJacobian Q = (jac H).map
      (algebraMap (MvPolynomial (Fin 4) K) (FractionRing (MvPolynomial (Fin 4) K))) :=
    rationalJacobian_polynomial H
  apply exists_fiber_equation_witness Q
  · rw [hJ]
    exact hN.map (algebraMap (MvPolynomial (Fin 4) K)
      (FractionRing (MvPolynomial (Fin 4) K))).mapMatrix
  · rw [hJ]
    exact hrank

end DimensionFourDependence
