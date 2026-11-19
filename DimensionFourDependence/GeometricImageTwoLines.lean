import DimensionFourDependence.GeometricNormalizedDirections
import DimensionFourDependence.RealizedCoefficientExtension
import DimensionFourDependence.IndependentGraphLines
import DimensionFourDependence.ImageIsotropicLine

/-! # Two distinct lines through the actual generic image point

The normalized directions on a nonlinear generic fiber lie in the
constructed algebraic coefficient extension. Their extended derivatives
integrate to lines on every actual image equation. Independence modulo
the radial point makes their full projective-line spans distinct.
-/

namespace DimensionFourDependence

open MvPolynomial Matrix

variable {K : Type*} [Field K] [CharZero K]

/-- Construct two genuine distinct lines through the actual generic
output value on its image equation. All direction, normalization,
coefficient-extension and line-integration data are derived; the
coefficient Hessian rank-two assumption remains explicit. -/
theorem geometric_fiber_image_contains_two_distinct_lines
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
    (hHess : (coefficientHessian (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K)
      (FractionRing (MvPolynomial (Fin 4) K)) (H (W.chart i.castSucc))) W.independent h).rank = 2)
    (E : Type*) [Field E] [IsAlgClosed E] [Algebra (polynomialOutputField H) E]
    [Algebra K E] [IsScalarTower K (polynomialOutputField H) E] [Algebra.IsAlgebraic (polynomialOutputField H) E]
    (P : Ideal (MvPolynomial (Fin 4) E)) [P.IsPrime]
    (hP : P ∈ (extendCoefficientIdeal E (fiberVanishingIdeal
      (L := polynomialOutputField H) (rationalCoordinate (K := K) (n := 4)))).minimalPrimes)
    (hline : ¬ LiesInAffineLine (E := E) (primeQuotientCoordinate P))
    (I : ImageRelationWitness H) :
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
  let : CharZero E := charZero_of_injective_algebraMap (algebraMap K E).injective
  let Q : Fin 4 → FractionRing (MvPolynomial (Fin 4) K) := fun i =>
    algebraMap (MvPolynomial (Fin 4) K) _ (H i)
  let Y : Fin 3 → FractionRing (MvPolynomial (Fin 4) K) := fun i => Q (W.chart i.castSucc)
  let L := coefficientField (K := K) Y
  have hr : (rationalJacobian Q).rank = 3 := by rw [rationalJacobian_polynomial H]; exact hrank
  obtain ⟨R, hRank, U, V, b, e, hUa, hUb, _, hVa, hVe, _, hQU, hQV, hCU, hCV, _, hli⟩ :=
    geometric_fiber_exists_normalized_isotropic_directions H hd hH hN hrank hind W h c q k
      hh hc hq hk hHess E P hP hline
  let : Algebra L E := R.coefficientMap.toAlgebra
  let : IsScalarTower K L E := R.scalarTower
  let : Algebra.IsAlgebraic L E := R.algebraic_extension Q hr W h c q k hh (primeQuotientCoordinate P)
  let y : Fin 3 → E := fun i => R.coefficientMap (coefficientCoordinate (K := K) Y i)
  let k₁ : E := ∑ i, U i * R.coefficientMap (coefficientGradient Y W.independent h i)
  let k₂ : E := ∑ i, V i * R.coefficientMap (coefficientGradient Y W.independent h i)
  let O : Fin 4 → E := (Fin.snoc y (R.coefficientMap h)) ∘ W.chart.symm
  let D₁ : Fin 4 → E := (Fin.snoc U k₁) ∘ W.chart.symm
  let D₂ : Fin 4 → E := (Fin.snoc V k₂) ∘ W.chart.symm
  have hy : y = fun i : Fin 3 => genericOutputValue H E (W.chart i.castSucc) :=
    funext (fun i => R.coordinate_image i)
  have hli3 : LinearIndependent E ![y, U, V] := by rw [hy]; exact hli
  have hli4 : LinearIndependent E ![O, D₁, D₂] :=
    independent_triple_precompose_equiv _ _ _
      (graph_lifts_triple_independent y U V hli3 (R.coefficientMap h) k₁ k₂) W.chart.symm
  have hO : O = genericOutputValue H E := by
    funext j
    obtain ⟨i, rfl⟩ := W.chart.surjective j
    simp only [O, Function.comp_apply, W.chart.symm_apply_apply]
    refine Fin.lastCases ?_ (fun i => ?_) i
    · simp only [Fin.snoc_last]
      change R.coefficientMap h = genericOutputValue H E (W.chart 3)
      exact R.last_output_image
    · simp only [Fin.snoc_castSucc]
      exact R.coordinate_image i
  have hUline := ImageRelationWitness.normalized_isotropic_line H W.chart W.independent
    hd hH h hh I E hRank U 2 b hUa hUb hQU hCU
  have hVline := ImageRelationWitness.normalized_isotropic_line H W.chart W.independent
    hd hH h hh I E hRank V 2 e hVa hVe hQV hCV
  change aeval (fun j => Polynomial.C (O j) + Polynomial.C (D₁ j) * Polynomial.X) I.equation = 0 at hUline
  change aeval (fun j => Polynomial.C (O j) + Polynomial.C (D₂ j) * Polynomial.X) I.equation = 0 at hVline
  exact ⟨R, U, V, hO, hUline, hVline, hli4, line_spans_distinct_of_independent_triple O D₁ D₂ hli4⟩

end DimensionFourDependence
