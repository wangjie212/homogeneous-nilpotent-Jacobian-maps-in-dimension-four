import DimensionFourDependence.GeometricFiberIsotropicDirections
import DimensionFourDependence.NormalizedIsotropicPair
import DimensionFourDependence.RadialRankTwoBaseChange

/-! # Normalized directions on the actual geometric generic component

The two directions (3.4) are normalized to zero in their third coordinate
and one in a surviving coordinate. The actual output's third coordinate
is nonzero by algebraic independence. The Hessian rank after extension
is derived, so both directions are ready for the line-integration step.
-/

namespace DimensionFourDependence

open MvPolynomial Matrix

variable {K : Type*} [Field K] [CharZero K]

/-- Construct both normalized directions of (3.4) and the required
extended Hessian rank directly from the actual nonlinear component. -/
theorem geometric_fiber_exists_normalized_isotropic_directions
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
    [Algebra K E] [IsScalarTower K (polynomialOutputField H) E]
    (P : Ideal (MvPolynomial (Fin 4) E)) [P.IsPrime]
    (hP : P ∈ (extendCoefficientIdeal E (fiberVanishingIdeal
      (L := polynomialOutputField H) (rationalCoordinate (K := K) (n := 4)))).minimalPrimes)
    (hline : ¬ LiesInAffineLine (E := E) (primeQuotientCoordinate P)) :
    ∃ R : FiberCoefficientRealization W.chart
        (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K)
          (FractionRing (MvPolynomial (Fin 4) K)) (H (W.chart i.castSucc)))
        W.independent h c q k (primeQuotientCoordinate P) (genericOutputValue H E),
      let T := (coefficientHessian (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K)
        (FractionRing (MvPolynomial (Fin 4) K)) (H (W.chart i.castSucc))) W.independent h).map R.coefficientMap
      let C := fun i j l => R.coefficientMap (coefficientCubicTensor
        (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K)
          (FractionRing (MvPolynomial (Fin 4) K)) (H (W.chart i.castSucc))) W.independent h i j l)
      T.rank = 2 ∧ ∃ (U V : Fin 3 → E) (b e : Fin 3),
        U 2 = 0 ∧ U b = 1 ∧ b ≠ 2 ∧ V 2 = 0 ∧ V e = 1 ∧ e ≠ 2 ∧
        matrixBilinearPairing T U U = 0 ∧ matrixBilinearPairing T V V = 0 ∧
        tensorTrilinearPairing C U U U = 0 ∧ tensorTrilinearPairing C V V V = 0 ∧
        matrixBilinearPairing T U V ≠ 0 ∧
        LinearIndependent E ![(fun i : Fin 3 => genericOutputValue H E (W.chart i.castSucc)), U, V] := by
  let Y : Fin 3 → FractionRing (MvPolynomial (Fin 4) K) := fun i =>
    algebraMap (MvPolynomial (Fin 4) K) _ (H (W.chart i.castSucc))
  have hEuler := homogeneous_last_output_euler H hd hH W.chart W.independent h hh
  obtain ⟨R, Z, V, hZ, hV, hκ, _, hCZ, hCV⟩ :=
    geometric_fiber_exists_two_isotropic_directions H hd hH hN hrank hind W h c q k
      hh hc hq hk hHess E P hP hline
  let L := coefficientField (K := K) Y
  let : Algebra L E := R.coefficientMap.toAlgebra
  let T := (coefficientHessian Y W.independent h).map R.coefficientMap
  let C := fun i j l => R.coefficientMap (coefficientCubicTensor Y W.independent h i j l)
  let y : Fin 3 → E := fun i => genericOutputValue H E (W.chart i.castSucc)
  have hT (i j : Fin 3) : T i j = T j i :=
    congrArg R.coefficientMap (coefficientHessian_symmetric Y W.independent h i j)
  have h12 (i j l : Fin 3) : C i j l = C j i l :=
    congrArg R.coefficientMap (coefficientCubicTensor_swap12 Y W.independent h i j l)
  have h23 (i j l : Fin 3) : C i j l = C i l j :=
    congrArg R.coefficientMap (coefficientCubicTensor_swap23 Y W.independent h i j l)
  have hcoords : (fun i : Fin 3 => R.coefficientMap (coefficientCoordinate (K := K) Y i)) = y :=
    funext (fun i => R.coordinate_image i)
  have hYpair (v : Fin 3 → E) : matrixBilinearPairing T y v = 0 := by
    have he := matrixBilinearPairing_radical_map (coefficientHessian Y W.independent h)
      (coefficientCoordinate (K := K) Y) (coefficientHessian_radial_contraction Y W.independent h hEuler) v
    change matrixBilinearPairing T (fun i => R.coefficientMap (coefficientCoordinate (K := K) Y i)) v = 0 at he
    rw [hcoords] at he
    exact he
  have hCYpair (v w : Fin 3 → E) : tensorTrilinearPairing C y v w = -matrixBilinearPairing T v w := by
    have he := tensorTrilinearPairing_radial_map (coefficientHessian Y W.independent h)
      (coefficientCubicTensor Y W.independent h) (coefficientCoordinate (K := K) Y)
      (coefficientCubicTensor_radial_contraction Y W.independent h hEuler) v w
    change tensorTrilinearPairing C (fun i => R.coefficientMap (coefficientCoordinate (K := K) Y i)) v w =
      -matrixBilinearPairing T v w at he
    rw [hcoords] at he
    exact he
  have hy2 : y 2 ≠ 0 := by
    intro hz
    have he : R.coefficientMap (coefficientCoordinate (K := K) Y 2) = 0 := (R.coordinate_image 2).trans hz
    have hzero : coefficientCoordinate (K := K) Y 2 = 0 := R.coefficientMap.injective
      (by simpa only [map_zero] using he)
    apply (W.independent.transcendental 2).ne_zero
    simpa only [coefficientCoordinate_coe, IntermediateField.coe_zero] using
      congrArg (fun z : L => (z : FractionRing (MvPolynomial (Fin 4) K))) hzero
  refine ⟨R, ?_, ?_⟩
  · exact coefficientHessian_rank_two_map Y W.independent h hEuler hHess E
  · exact exists_normalized_isotropic_pair T C hT h12 h23 y
      (fun i : Fin 3 => Z (W.chart i.castSucc)) (fun i : Fin 3 => V (W.chart i.castSucc))
      2 hy2 hYpair hCYpair hZ hV hκ hCZ hCV

end DimensionFourDependence
