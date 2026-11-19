import DimensionFourDependence.TernaryGraphPlaneDifferentiation

/-! # The actual quadratic invariant of the embedded ternary generic curve -/

namespace DimensionFourDependence

open MvPolynomial Matrix

set_option maxHeartbeats 1850000

variable {K : Type*} [Field K] [CharZero K]
local notation "F" => FractionRing (MvPolynomial (Fin 3) K)
local notation "x" => (rationalCoordinate (K := K) (n := 3))

noncomputable def ternaryGraphQuadraticValue (Y : Fin 2 → F) (hY : AlgebraicIndependent K Y)
    (w s : coefficientField (K := K) Y) : F :=
  quadraticExpression (fun i : Fin 2 => (coefficientPartial Y hY i s : F))
    (ternaryGraphHessian Y hY w) (fun i : Fin 2 => x i.castSucc)

theorem ternaryGraphQuadraticValue_mem_coefficientField
    (Y : Fin 2 → F) (hY : AlgebraicIndependent K Y) (w s : coefficientField (K := K) Y)
    (hs : (s : F) = ternaryGraphPlaneValue Y hY w)
    (hN : IsNilpotent (rationalJacobian (![Y 0, Y 1, (w : F)] : Fin 3 → F))) :
    ternaryGraphQuadraticValue Y hY w s ∈ coefficientField (K := K) Y := by
  let D := ternaryJacobianDerivation (K := K) (Y 0) (Y 1)
  let p := ternaryGraphGradient Y hY w 0
  let q := ternaryGraphGradient Y hY w 1
  let u := ternaryRationalGradient (Y 0)
  let v := ternaryRationalGradient (Y 1)
  let A := ternaryGraphAffineGradient Y hY w s
  let C₀ := ternaryCrossProduct u v
  have hy := ternaryJacobianDerivation_kills_pair Y
  have hds (i : Fin 2) : D (coefficientPartial Y hY i s : F) = 0 :=
    vertical_derivation_kills_coefficient_field Y D hy (coefficientPartial Y hY i s)
  have hdw (i j : Fin 2) : D (ternaryGraphHessian Y hY w i j) = 0 :=
    vertical_derivation_kills_coefficient_field Y D hy
      (coefficientPartial Y hY i (coefficientPartial Y hY j w))
  have h₀ : A 0 * u 0 + A 1 * v 0 = -p := ternaryGraphPlane_coordinate_partials Y hY w s hs 0
  have h₁ : A 0 * u 1 + A 1 * v 1 = -q := ternaryGraphPlane_coordinate_partials Y hY w s hs 1
  have h₂ : A 0 * u 2 + A 1 * v 2 = 1 := ternaryGraphPlane_coordinate_partials Y hY w s hs 2
  have hgraph : IsNilpotent (ternaryGraphMatrix u v p q) := by
    rw [ternaryGraph_rationalJacobian Y hY w] at hN
    exact hN
  have htrace := (Matrix.isNilpotent_trace_of_isNilpotent hgraph).eq_zero
  rw [ternaryGraphMatrix_trace_from_plane_derivatives u v (A 0) (A 1) p q h₀ h₁ h₂] at htrace
  have hc : A 0 * C₀ 0 + A 1 * C₀ 1 = 0 := by
    change -A 0 * C₀ 0 - A 1 * C₀ 1 = 0 at htrace
    linear_combination -htrace
  have hD : D (ternaryGraphQuadraticValue Y hY w s) = 0 := by
    unfold ternaryGraphQuadraticValue
    rw [quadraticExpression_deriv D _ _ _ hds hdw (ternaryGraphHessian_symmetric Y hY w)]
    change ∑ i : Fin 2, A i * D (x i.castSucc) = 0
    have hCoord (j : Fin 3) : D (x j) = C₀ j := ternaryJacobianDerivation_apply_coordinate _ _ j
    rw [Fin.sum_univ_two, hCoord, hCoord]
    change A 0 * C₀ 0 + A 1 * C₀ 1 = 0
    exact hc
  have hmem : ternaryGraphQuadraticValue Y hY w s ∈
      derivationConstants (ternaryJacobianDerivation (Y 0) (Y 1)) := hD
  rw [ternaryJacobianDerivation_constants Y hY] at hmem
  exact hmem

/-- Both exact constants of (3.4) and (3.6) are elements of the same
relative algebraic closure over the actual selected output pair. -/
theorem nilpotent_ternary_graph_constructs_plane_and_quadratic_values
    (Y : Fin 2 → F) (hY : AlgebraicIndependent K Y) (w : coefficientField (K := K) Y)
    (hN : IsNilpotent (rationalJacobian (![Y 0, Y 1, (w : F)] : Fin 3 → F))) :
    ∃ s τ : coefficientField (K := K) Y,
      (s : F) = ternaryGraphPlaneValue Y hY w ∧ (τ : F) = ternaryGraphQuadraticValue Y hY w s := by
  let s : coefficientField (K := K) Y :=
    ⟨ternaryGraphPlaneValue Y hY w, ternaryGraphPlaneValue_mem_coefficientField Y hY w hN⟩
  let τ : coefficientField (K := K) Y :=
    ⟨ternaryGraphQuadraticValue Y hY w s, ternaryGraphQuadraticValue_mem_coefficientField Y hY w s rfl hN⟩
  exact ⟨s, τ, rfl, rfl⟩

end DimensionFourDependence
