import DimensionFourDependence.FiberInvariantTransport
import DimensionFourDependence.FullOutputGeometricFiber
import DimensionFourDependence.GenericOutputPoint

/-! # Actual coefficient data on every geometric generic component

The compatible source and coefficient embeddings construct all equations
over the component's constant field. The coefficient images of the
generic output and of the original base field are recorded explicitly.
-/

namespace DimensionFourDependence

open MvPolynomial Matrix

variable {K E G : Type*} [Field K] [CharZero K] [Field E] [Algebra K E]
    [Field G] [Algebra E G]

/-- The actual algebraic fiber coefficients realized as constants on
an embedded source point, with all three invariant equations verified. -/
structure FiberCoefficientRealization
    (p : Equiv.Perm (Fin 4)) (Y : Fin 3 → FractionRing (MvPolynomial (Fin 4) K))
    (hY : AlgebraicIndependent K Y) (h c q k : coefficientField (K := K) Y)
    (x : Fin 4 → G) (y : Fin 4 → E) where
  coefficientMap : coefficientField (K := K) Y →+* E
  scalar_image : ∀ r : K, coefficientMap (algebraMap K (coefficientField (K := K) Y) r) = algebraMap K E r
  coordinate_image : ∀ i : Fin 3, coefficientMap (coefficientCoordinate (K := K) Y i) = y (p i.castSucc)
  last_output_image : coefficientMap h = y (p 3)
  graph_equation : x (p 3) = (∑ i : Fin 3,
    algebraMap E G (coefficientMap (coefficientPartial Y hY i h)) * x (p i.castSucc)) +
      algebraMap E G (coefficientMap c)
  quadratic_equation : algebraMap E G (coefficientMap q) = quadraticExpression
    (fun i => algebraMap E G (coefficientMap (coefficientPartial Y hY i c)))
    (((coefficientHessian Y hY h).map coefficientMap).map (algebraMap E G))
    (fun i : Fin 3 => x (p i.castSucc))
  cubic_equation : aeval (fun i : Fin 3 => x (p i.castSucc))
    (cubicFiberPolynomial (fun i => coefficientMap (coefficientPartial Y hY i q))
      ((coefficientHessian Y hY c).map coefficientMap)
      (fun i j l => coefficientMap (coefficientCubicTensor Y hY h i j l)) (coefficientMap k)) = 0

omit [Field E] [Algebra K E] [Field G] [Algebra E G] in
/-- Every actual geometric generic component supplies a coefficient
realization of the constructed invariants in its original four source coordinates. -/
theorem exists_geometric_fiber_coefficient_realization
    (H : Fin 4 → MvPolynomial (Fin 4) K) (hrank : polyRank (jac H) = 3)
    (W : FiberEquationWitness (fun i => algebraMap (MvPolynomial (Fin 4) K)
      (FractionRing (MvPolynomial (Fin 4) K)) (H i)))
    (h c q k : coefficientField (K := K) (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K)
      (FractionRing (MvPolynomial (Fin 4) K)) (H (W.chart i.castSucc))))
    (hh : (h : FractionRing (MvPolynomial (Fin 4) K)) =
      algebraMap (MvPolynomial (Fin 4) K) _ (H (W.chart 3)))
    (hc : (c : FractionRing (MvPolynomial (Fin 4) K)) = firstFiberInvariantInChart W.chart
      (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K)
        (FractionRing (MvPolynomial (Fin 4) K)) (H (W.chart i.castSucc))) W.independent h)
    (hq : (q : FractionRing (MvPolynomial (Fin 4) K)) = secondFiberInvariant W.chart
      (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K)
        (FractionRing (MvPolynomial (Fin 4) K)) (H (W.chart i.castSucc))) W.independent h c)
    (hk : (k : FractionRing (MvPolynomial (Fin 4) K)) = thirdFiberInvariant W.chart
      (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K)
        (FractionRing (MvPolynomial (Fin 4) K)) (H (W.chart i.castSucc))) W.independent h c q)
    (A : Type*) [Field A] [Algebra (polynomialOutputField H) A] [Algebra K A]
    [IsScalarTower K (polynomialOutputField H) A] [IsAlgClosed A]
    (P : Ideal (MvPolynomial (Fin 4) A)) [P.IsPrime]
    (hP : P ∈ (extendCoefficientIdeal A (fiberVanishingIdeal
      (L := polynomialOutputField H) (rationalCoordinate (K := K) (n := 4)))).minimalPrimes) :
    Nonempty (FiberCoefficientRealization W.chart
      (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K)
        (FractionRing (MvPolynomial (Fin 4) K)) (H (W.chart i.castSucc)))
      W.independent h c q k (primeQuotientCoordinate P) (genericOutputValue H A)) := by
  let Q : Fin 4 → FractionRing (MvPolynomial (Fin 4) K) :=
    fun i => algebraMap (MvPolynomial (Fin 4) K) _ (H i)
  let Y : Fin 3 → FractionRing (MvPolynomial (Fin 4) K) := fun i => Q (W.chart i.castSucc)
  let L := coefficientField (K := K) Y
  let M := polynomialOutputField H
  let F := FractionRing (MvPolynomial (Fin 4) K)
  let B := FractionRing (MvPolynomial (Fin 4) A ⧸ P)
  have hr : (rationalJacobian Q).rank = 3 := by rw [rationalJacobian_polynomial H]; exact hrank
  let : Algebra M L := fullOutputCoefficientAlgebra Q hr W.chart W.independent
  let mBAlgebra : Algebra M B := inferInstance
  let : SMul M B := mBAlgebra.toSMul
  let : IsScalarTower M A B := inferInstance
  obtain ⟨f, hf, g, hg⟩ := full_output_geometric_coefficient_embedding Q hr W A P hP
  refine ⟨{
    coefficientMap := g.toRingHom
    scalar_image := ?_
    coordinate_image := ?_
    last_output_image := ?_
    graph_equation := firstFiberInvariant_transport Y W.independent f.toRingHom g.toRingHom hg
      W.chart h c hc (primeQuotientCoordinate P) hf
    quadratic_equation := secondFiberInvariant_transport Y W.independent f.toRingHom g.toRingHom hg
      W.chart h c q hq (primeQuotientCoordinate P) hf
    cubic_equation := thirdFiberInvariant_transport Y W.independent f.toRingHom g.toRingHom hg
      W.chart h c q k hk (primeQuotientCoordinate P) hf }⟩
  · intro r
    change g (algebraMap M L (algebraMap K M r)) = algebraMap K A r
    rw [g.commutes]
    exact (IsScalarTower.algebraMap_apply K M A r).symm
  · intro i
    change g (algebraMap M L (fullOutputCoordinate (K := K) Q (W.chart i.castSucc))) =
      algebraMap M A (fullOutputCoordinate (K := K) Q (W.chart i.castSucc))
    exact g.commutes _
  · have he : h = algebraMap M L (fullOutputCoordinate (K := K) Q (W.chart 3)) := by
      apply Subtype.ext
      exact hh
    change g h = algebraMap M A (fullOutputCoordinate (K := K) Q (W.chart 3))
    rw [he, g.commutes]

end DimensionFourDependence
