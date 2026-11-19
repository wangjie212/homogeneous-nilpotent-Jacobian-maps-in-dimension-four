import DimensionFourDependence.GeometricCoefficientNormalForm
import DimensionFourDependence.GenericFiberTwoCubicDirections
import DimensionFourDependence.GenericFiberHyperbolaCubicDirections
import DimensionFourDependence.ZeroInvariantGeometricFiber

/-! # Both actual isotropic directions from a nonlinear geometric generic fiber

The actual coefficient realization supplies all equations and Euler
data. The rank-two coefficient Hessian constructs the normal form.
Nonlinearity excludes the simultaneous-zero case, and the two verified
pole arguments give (3.4) in the remaining cases.
-/

namespace DimensionFourDependence

open MvPolynomial Matrix

variable {K : Type*} [Field K] [CharZero K]

/-- The actual nonlinear geometric component supplies both directions
of (3.4), with all embeddings, coefficients, coordinates, normal forms,
parameter variation and poles constructed. Only the rank-two Hessian
hypothesis remains from the Gauss-image reduction. -/
theorem geometric_fiber_exists_two_isotropic_directions
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
      ∃ Z V : Fin 4 → E,
        matrixBilinearPairing T (fun i : Fin 3 => Z (W.chart i.castSucc))
          (fun i : Fin 3 => Z (W.chart i.castSucc)) = 0 ∧
        matrixBilinearPairing T (fun i : Fin 3 => V (W.chart i.castSucc))
          (fun i : Fin 3 => V (W.chart i.castSucc)) = 0 ∧
        matrixBilinearPairing T (fun i : Fin 3 => Z (W.chart i.castSucc))
          (fun i : Fin 3 => V (W.chart i.castSucc)) ≠ 0 ∧
        LinearIndependent E ![(fun i : Fin 3 => genericOutputValue H E (W.chart i.castSucc)),
          (fun i : Fin 3 => Z (W.chart i.castSucc)), (fun i : Fin 3 => V (W.chart i.castSucc))] ∧
        tensorTrilinearPairing C (fun i : Fin 3 => Z (W.chart i.castSucc))
          (fun i : Fin 3 => Z (W.chart i.castSucc)) (fun i : Fin 3 => Z (W.chart i.castSucc)) = 0 ∧
        tensorTrilinearPairing C (fun i : Fin 3 => V (W.chart i.castSucc))
          (fun i : Fin 3 => V (W.chart i.castSucc)) (fun i : Fin 3 => V (W.chart i.castSucc)) = 0 := by
  let : CharZero E := charZero_of_injective_algebraMap (algebraMap K E).injective
  let Y : Fin 3 → FractionRing (MvPolynomial (Fin 4) K) := fun i =>
    algebraMap (MvPolynomial (Fin 4) K) _ (H (W.chart i.castSucc))
  let G := FractionRing (MvPolynomial (Fin 4) E ⧸ P)
  let θ : K := (d : K)⁻¹
  have hθ : θ ≠ 0 := inv_ne_zero (Nat.cast_ne_zero.mpr (by omega))
  have hθE : algebraMap K E θ ≠ 0 := by
    simpa only [map_zero] using (algebraMap K E).injective.ne hθ
  have hEuler := homogeneous_last_output_euler H hd hH W.chart W.independent h hh
  have hcEuler := firstFiberInvariant_output_weight H hd hH W.chart W.independent h c hh hc
  obtain ⟨R⟩ := exists_geometric_fiber_coefficient_realization H hrank W h c q k hh hc hq hk E P hP
  let T := (coefficientHessian Y W.independent h).map R.coefficientMap
  let C := fun i j l => R.coefficientMap (coefficientCubicTensor Y W.independent h i j l)
  obtain ⟨Z, V, τ, s, t, hZ, hV, hκ, hli, hx, heq⟩ :=
    R.exists_isotropic_normal_form θ hEuler hcEuler hHess
  obtain ⟨_, _, hRad, hCY⟩ := R.radial_data θ hEuler hcEuler
  have h12 (i j l : Fin 3) : C i j l = C j i l :=
    congrArg R.coefficientMap (coefficientCubicTensor_swap12 Y W.independent h i j l)
  have h23 (i j l : Fin 3) : C i j l = C i l j :=
    congrArg R.coefficientMap (coefficientCubicTensor_swap23 Y W.independent h i j l)
  let a : E := algebraMap K E θ * R.coefficientMap c
  let α : E := ∑ i : Fin 3, R.coefficientMap (coefficientPartial Y W.independent i c) * Z (W.chart i.castSucc)
  let β : E := ∑ i : Fin 3, R.coefficientMap (coefficientPartial Y W.independent i c) * V (W.chart i.castSucc)
  let κ : E := matrixBilinearPairing T (fun i : Fin 3 => Z (W.chart i.castSucc))
    (fun i : Fin 3 => V (W.chart i.castSucc))
  let v₀ : Fin 4 → E := Pi.single (W.chart 3) (R.coefficientMap c)
  have heq' : algebraMap E G (R.coefficientMap q) = algebraMap E G a * τ +
      algebraMap E G α * s + algebraMap E G β * t + algebraMap E G κ * s * t := by
    simpa only [a, α, β, κ, map_mul] using heq
  have hnonzero := nonlinear_geometric_component_invariants_nonzero H hd hH hN hrank W
    h c q hh hc hq E P hP hline
  refine ⟨R, Z, V, hZ, hV, hκ, hli, ?_⟩
  by_cases hc0 : c = 0
  · have hq0 : q ≠ 0 := by
      rcases hnonzero with hcne | hqne
      · exact False.elim (hcne hc0)
      · exact hqne
    have hqE : R.coefficientMap q ≠ 0 := by
      simpa only [map_zero] using R.coefficientMap.injective.ne hq0
    have ha0 : a = 0 := by simp only [a, hc0, map_zero, mul_zero]
    have hα0 : α = 0 := by simp only [α, hc0, map_zero, zero_mul, Finset.sum_const_zero]
    have hβ0 : β = 0 := by simp only [β, hc0, map_zero, zero_mul, Finset.sum_const_zero]
    have hhyperbola : algebraMap E G (R.coefficientMap q) = algebraMap E G κ * s * t := by
      simpa only [ha0, hα0, hβ0, map_zero, zero_mul, zero_add] using heq'
    exact generic_fiber_nonlinear_hyperbola_cubic_directions H hd hH hN hrank hind E P hP
      τ s t Z V v₀ κ (R.coefficientMap q) hκ hqE hx hhyperbola hline
      (fun i : Fin 3 => W.chart i.castSucc) T C h12 h23 hRad hCY hZ hV
      (fun i => R.coefficientMap (coefficientPartial Y W.independent i q))
      ((coefficientHessian Y W.independent c).map R.coefficientMap) (R.coefficientMap k) R.cubic_equation
  · have hcE : R.coefficientMap c ≠ 0 := by
      simpa only [map_zero] using R.coefficientMap.injective.ne hc0
    have ha : a ≠ 0 := mul_ne_zero hθE hcE
    exact generic_fiber_nonlinear_nonzero_radial_cubic_directions H hd hH hN hrank hind E P hP
      τ s t Z V v₀ a α β κ (R.coefficientMap q) ha hκ hx heq' hline
      (fun i : Fin 3 => W.chart i.castSucc) T C h12 h23 hRad hCY hZ hV
      (fun i => R.coefficientMap (coefficientPartial Y W.independent i q))
      ((coefficientHessian Y W.independent c).map R.coefficientMap) (R.coefficientMap k) R.cubic_equation

end DimensionFourDependence
