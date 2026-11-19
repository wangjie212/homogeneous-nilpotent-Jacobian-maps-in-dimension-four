import DimensionFourDependence.GeometricGaussTwoLines
import DimensionFourDependence.ProjectiveLineAtlasPoints

/-! # Actual generic image lines as points of the hypersurface line atlas

The Gauss-dimension-two construction produces two distinct atlas points
representing distinct projective lines through the actual generic image
value. No projective span containment, chart choice or parameter-space
membership is left as an additional hypothesis.
-/

namespace DimensionFourDependence

open MvPolynomial Matrix

variable {K : Type*} [Field K] [CharZero K]

/-- The original Gauss-dimension-two and nonlinear-fiber hypotheses
supply two distinct actual points of the image hypersurface's line atlas. -/
theorem geometric_fiber_two_actual_line_atlas_points
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
    ∃ s₁ s₂ : hypersurfaceLineAtlas (MvPolynomial.map (algebraMap K E) I.equation),
      s₁ ≠ s₂ ∧ hypersurfaceAtlasLine _ s₁ ≠ hypersurfaceAtlasLine _ s₂ ∧
      genericOutputValue H E ∈ hypersurfaceAtlasLine _ s₁ ∧
      genericOutputValue H E ∈ hypersurfaceAtlasLine _ s₂ := by
  let : CharZero E := charZero_of_injective_algebraMap (algebraMap K E).injective
  obtain ⟨R, U, V, hO, hline₁, hline₂, hli, _⟩ :=
    geometric_fiber_two_lines_of_gauss_dimension_two H hd hH hN hrank hind W h c q k
      hh hc hq hk E P hP hline I hGauss
  obtain ⟨s₁, s₂, _, _, hneq, hsneq, hmem₁, hmem₂⟩ :=
    two_homogeneous_affine_lines_atlas_points I.equation I.homogeneous _ _ _ hli hline₁ hline₂
  refine ⟨s₁, s₂, hsneq, hneq, ?_, ?_⟩
  · simpa only [hO] using hmem₁
  · simpa only [hO] using hmem₂

end DimensionFourDependence
