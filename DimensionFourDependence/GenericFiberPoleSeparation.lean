import DimensionFourDependence.DominantRadialResidue

/-! # Simultaneous poles are impossible in the nonzero-radial normal form

The quadratic normal form, full-source affine decomposition and actual
radial exclusion imply the simultaneous-pole assertion of Section 3.2.
The existence of the isotropic coordinates remains a separate step.
-/

namespace DimensionFourDependence

open MvPolynomial

variable {K : Type*} [Field K] [CharZero K]

/-- For an actual geometric generic component of a nonlinear image,
the two isotropic coordinates in (3.3) cannot have a simultaneous pole
when the radial and mixed coefficients are nonzero. -/
theorem generic_fiber_quadratic_no_simultaneous_poles
    (H : Fin 4 → MvPolynomial (Fin 4) K) {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d)
    (hN : IsNilpotent (jac H)) (hrank : polyRank (jac H) = 3) (hind : ¬ ComponentsDependent H)
    (E : Type*) [Field E] [Algebra (polynomialOutputField H) E]
    [Algebra K E] [IsScalarTower K (polynomialOutputField H) E]
    (P : Ideal (MvPolynomial (Fin 4) E)) [P.IsPrime]
    (hP : P ∈ (extendCoefficientIdeal E (fiberVanishingIdeal
      (L := polynomialOutputField H) (rationalCoordinate (K := K) (n := 4)))).minimalPrimes)
    (V : ValuationSubring (FractionRing (MvPolynomial (Fin 4) E ⧸ P))) [Algebra E V] :
    let G := FractionRing (MvPolynomial (Fin 4) E ⧸ P)
    let vGAlgebra : Algebra V G := inferInstance
    letI : SMul V G := vGAlgebra.toSMul
    ∀ [IsScalarTower E V G] (τ s t : G) (Z W c : Fin 4 → E) (a α β κ q : E),
      a ≠ 0 → κ ≠ 0 →
      (∀ i, primeQuotientCoordinate P i = τ * algebraMap E G (genericOutputValue H E i) +
        s * algebraMap E G (Z i) + t * algebraMap E G (W i) + algebraMap E G (c i)) →
      (algebraMap E G q = algebraMap E G a * τ + algebraMap E G α * s +
        algebraMap E G β * t + algebraMap E G κ * s * t) →
      1 < V.valuation s → 1 < V.valuation t → False := by
  let G := FractionRing (MvPolynomial (Fin 4) E ⧸ P)
  let vGAlgebra : Algebra V G := inferInstance
  let : SMul V G := vGAlgebra.toSMul
  dsimp only
  intro hTower τ s t Z W c a α β κ q ha hκ hpos heq hs ht
  have hconstants (b : E) : V.valuation (algebraMap E G b) ≤ 1 := by
    apply (V.valuation_le_one_iff _).mpr
    have he : algebraMap V G (algebraMap E V b) = algebraMap E G b :=
      (IsScalarTower.algebraMap_apply E V G b).symm
    rw [← he]
    exact (algebraMap E V b).property
  let : V.valuation.IsTrivialOn E := Valuation.IsTrivialOn.of_le_one V.valuation hconstants
  obtain ⟨_, hvs, hvt, hτ⟩ := quadratic_normal_form_simultaneous_poles V.valuation
    a α β κ q ha hκ τ s t heq hs ht
  let error : Fin 4 → G := fun i => s * algebraMap E G (Z i) +
    t * algebraMap E G (W i) + algebraMap E G (c i)
  have herr : ∀ i, V.valuation (error i) < V.valuation τ :=
    affine_isotropic_errors_below_radial V Z W c τ s t hτ hvs hvt
  have hsource (i : Fin 4) : primeQuotientCoordinate P i =
      τ * algebraMap E G (genericOutputValue H E i) + error i := by
    rw [hpos i]
    change τ * algebraMap E G (genericOutputValue H E i) + s * algebraMap E G (Z i) +
      t * algebraMap E G (W i) + algebraMap E G (c i) = _
    dsimp only [error]
    ring
  obtain ⟨z, hz, hres⟩ := dominant_radial_term_has_radial_residue V
    (primeQuotientCoordinate P) error (genericOutputValue H E) τ hτ herr hsource
  exact radial_generic_output_not_valuation_residue H hd hH hN hrank hind E P hP V τ⁻¹ z hz hres

end DimensionFourDependence
