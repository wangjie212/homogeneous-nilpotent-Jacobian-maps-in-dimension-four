import DimensionFourDependence.GeometricImageTwoLines
import DimensionFourDependence.GaussImageDimension

/-! # The two-line conclusion from the actual Gauss-image dimension

The Gauss-image function field supplies the coefficient Hessian rank,
so the complete two-line construction now starts from the paper's
Gauss-dimension hypothesis instead of an extra Hessian-rank assumption.
The doubly ruled quadric classification remains a separate obligation.
-/

namespace DimensionFourDependence

open MvPolynomial Matrix

variable {K : Type*} [Field K] [CharZero K]

/-- A two-dimensional actual Gauss image and a nonlinear geometric
fiber give two distinct image lines through the actual generic image point. -/
theorem geometric_fiber_two_lines_of_gauss_dimension_two
    (H : Fin 4 → MvPolynomial (Fin 4) K) {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d)
    (hN : IsNilpotent (jac H)) (hrank : polyRank (jac H) = 3) (hind : ¬ ComponentsDependent H)
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
    (E : Type*) [Field E] [IsAlgClosed E] [Algebra (polynomialOutputField H) E]
    [Algebra K E] [IsScalarTower K (polynomialOutputField H) E] [Algebra.IsAlgebraic (polynomialOutputField H) E]
    (P : Ideal (MvPolynomial (Fin 4) E)) [P.IsPrime]
    (hP : P ∈ (extendCoefficientIdeal E (fiberVanishingIdeal
      (L := polynomialOutputField H) (rationalCoordinate (K := K) (n := 4)))).minimalPrimes)
    (hline : ¬ LiesInAffineLine (E := E) (primeQuotientCoordinate P))
    (I : ImageRelationWitness H) (hGauss : gaussImageDimension H I = 2) :
    ∃ R : FiberCoefficientRealization W.chart
        (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K)
          (FractionRing (MvPolynomial (Fin 4) K)) (H (W.chart i.castSucc)))
        W.independent h c q k (primeQuotientCoordinate P) (genericOutputValue H E),
      ∃ U V : Fin 3 → E,
        let O : Fin 4 → E := (Fin.snoc
          (fun i => R.coefficientMap (coefficientCoordinate (K := K)
            (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K)
              (FractionRing (MvPolynomial (Fin 4) K)) (H (W.chart i.castSucc))) i))
          (R.coefficientMap h)) ∘ W.chart.symm
        let D₁ : Fin 4 → E := (Fin.snoc U (∑ i, U i * R.coefficientMap (coefficientGradient
          (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K)
            (FractionRing (MvPolynomial (Fin 4) K)) (H (W.chart i.castSucc))) W.independent h i))) ∘ W.chart.symm
        let D₂ : Fin 4 → E := (Fin.snoc V (∑ i, V i * R.coefficientMap (coefficientGradient
          (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K)
            (FractionRing (MvPolynomial (Fin 4) K)) (H (W.chart i.castSucc))) W.independent h i))) ∘ W.chart.symm
        O = genericOutputValue H E ∧
        aeval (fun j => Polynomial.C (O j) + Polynomial.C (D₁ j) * Polynomial.X) I.equation = 0 ∧
        aeval (fun j => Polynomial.C (O j) + Polynomial.C (D₂ j) * Polynomial.X) I.equation = 0 ∧
        LinearIndependent E ![O, D₁, D₂] ∧
        Submodule.span E (Set.range ![O, D₁]) ≠ Submodule.span E (Set.range ![O, D₂]) := by
  have hHess := (I.gauss_dimension_two_iff_hessian_rank_two H W.chart W.independent h hh).mp hGauss
  exact geometric_fiber_image_contains_two_distinct_lines H hd hH hN hrank hind W h c q k
    hh hc hq hk hHess E P hP hline I

end DimensionFourDependence
