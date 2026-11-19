import DimensionFourDependence.RadialPoleBound

/-! # Single-pole bounds on the actual geometric generic fiber

The actual radial exclusion bounds the radial parameter. In the
nonzero-radial quadratic normal form, the simultaneous-pole contradiction
also makes the other isotropic parameter finite.
-/

namespace DimensionFourDependence

open MvPolynomial

variable {K : Type*} [Field K] [CharZero K]

section

variable (H : Fin 4 → MvPolynomial (Fin 4) K) {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d)
    (hN : IsNilpotent (jac H)) (hrank : polyRank (jac H) = 3) (hind : ¬ ComponentsDependent H)
    (E : Type*) [Field E] [Algebra (polynomialOutputField H) E]
    [Algebra K E] [IsScalarTower K (polynomialOutputField H) E]
    (P : Ideal (MvPolynomial (Fin 4) E)) [P.IsPrime]
    (hP : P ∈ (extendCoefficientIdeal E (fiberVanishingIdeal
      (L := polynomialOutputField H) (rationalCoordinate (K := K) (n := 4)))).minimalPrimes)

local notation "G" => FractionRing (MvPolynomial (Fin 4) E ⧸ P)

include hd hH hN hrank hind hP

/-- The radial parameter of an actual component is never strictly
dominant in a full-source affine decomposition of the stated form. -/
theorem generic_fiber_radial_value_bound (V : ValuationSubring G) [Algebra E V] :
    let vGAlgebra : Algebra V G := inferInstance
    letI : SMul V G := vGAlgebra.toSMul
    ∀ [IsScalarTower E V G] (τ s t : G) (Z W c : Fin 4 → E),
      (∀ i, primeQuotientCoordinate P i = τ * algebraMap E G (genericOutputValue H E i) +
        s * algebraMap E G (Z i) + t * algebraMap E G (W i) + algebraMap E G (c i)) →
      V.valuation τ ≤ max (max 1 (V.valuation s)) (V.valuation t) := by
  let vGAlgebra : Algebra V G := inferInstance
  let : SMul V G := vGAlgebra.toSMul
  dsimp only
  intro hTower τ s t Z W c hx
  exact radial_coordinate_value_bound (primeQuotientCoordinate P) (genericOutputValue H E) Z W c
    (radialGenericOutputVector_ne_zero H (rank_three_polynomial_map_ne_zero H hrank) E)
    (radial_generic_output_not_in_geometric_fiber_closure H hd hH hN hrank hind E P hP)
    V τ s t hx

/-- At a pole of `s` in (3.3), `t` is finite and `tau` has at most
the same pole order as `s`, for the actual geometric component. -/
theorem generic_fiber_single_pole_bounds (V : ValuationSubring G) [Algebra E V] :
    let vGAlgebra : Algebra V G := inferInstance
    letI : SMul V G := vGAlgebra.toSMul
    ∀ [IsScalarTower E V G] (τ s t : G) (Z W c : Fin 4 → E) (a α β κ q : E),
      a ≠ 0 → κ ≠ 0 →
      (∀ i, primeQuotientCoordinate P i = τ * algebraMap E G (genericOutputValue H E i) +
        s * algebraMap E G (Z i) + t * algebraMap E G (W i) + algebraMap E G (c i)) →
      (algebraMap E G q = algebraMap E G a * τ + algebraMap E G α * s +
        algebraMap E G β * t + algebraMap E G κ * s * t) →
      1 < V.valuation s → V.valuation t ≤ 1 ∧ V.valuation τ ≤ V.valuation s := by
  let vGAlgebra : Algebra V G := inferInstance
  let : SMul V G := vGAlgebra.toSMul
  dsimp only
  intro hTower τ s t Z W c a α β κ q ha hκ hx heq hs
  have ht : V.valuation t ≤ 1 := le_of_not_gt (fun ht =>
    generic_fiber_quadratic_no_simultaneous_poles H hd hH hN hrank hind E P hP V
      τ s t Z W c a α β κ q ha hκ hx heq hs ht)
  have he := generic_fiber_radial_value_bound H hd hH hN hrank hind E P hP V τ s t Z W c hx
  rw [max_eq_right hs.le, max_eq_left (ht.trans hs.le)] at he
  exact ⟨ht, he⟩

end

end DimensionFourDependence
