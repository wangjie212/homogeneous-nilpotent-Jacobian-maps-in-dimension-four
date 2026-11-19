import DimensionFourDependence.QuadraticParameterNonconstancy

/-! # Both cubic directions in the nonzero-radial quadratic normal form

For an actual nonlinear geometric generic component, nonlinearity
supplies the two nonscalar parameters, each supplies a pole, and the
single-pole argument gives both constant cubic equations (3.4).
The normal-form and Euler coefficient data are stated explicitly.
-/

namespace DimensionFourDependence

open MvPolynomial

variable {K : Type*} [Field K] [CharZero K]

/-- The nonzero-radial normal-form branch yields the two cubic
directions from an actual nonlinear generic component, with no pole,
valuation or parameter-nonscalarity hypothesis left to supply. -/
theorem generic_fiber_nonlinear_nonzero_radial_cubic_directions
    (H : Fin 4 → MvPolynomial (Fin 4) K) {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d)
    (hN : IsNilpotent (jac H)) (hrank : polyRank (jac H) = 3) (hind : ¬ ComponentsDependent H)
    (E : Type*) [Field E] [CharZero E] [IsAlgClosed E] [Algebra (polynomialOutputField H) E]
    [Algebra K E] [IsScalarTower K (polynomialOutputField H) E]
    (P : Ideal (MvPolynomial (Fin 4) E)) [P.IsPrime]
    (hP : P ∈ (extendCoefficientIdeal E (fiberVanishingIdeal
      (L := polynomialOutputField H) (rationalCoordinate (K := K) (n := 4)))).minimalPrimes)
    (τ s t : FractionRing (MvPolynomial (Fin 4) E ⧸ P))
    (Z W c : Fin 4 → E) (a α β κ q : E) (ha : a ≠ 0) (hκ : κ ≠ 0)
    (hx : ∀ i, primeQuotientCoordinate P i =
      τ * algebraMap E (FractionRing (MvPolynomial (Fin 4) E ⧸ P)) (genericOutputValue H E i) +
      s * algebraMap E (FractionRing (MvPolynomial (Fin 4) E ⧸ P)) (Z i) +
      t * algebraMap E (FractionRing (MvPolynomial (Fin 4) E ⧸ P)) (W i) +
      algebraMap E (FractionRing (MvPolynomial (Fin 4) E ⧸ P)) (c i))
    (heq : algebraMap E (FractionRing (MvPolynomial (Fin 4) E ⧸ P)) q =
      algebraMap E (FractionRing (MvPolynomial (Fin 4) E ⧸ P)) a * τ +
      algebraMap E (FractionRing (MvPolynomial (Fin 4) E ⧸ P)) α * s +
      algebraMap E (FractionRing (MvPolynomial (Fin 4) E ⧸ P)) β * t +
      algebraMap E (FractionRing (MvPolynomial (Fin 4) E ⧸ P)) κ * s * t)
    (hline : ¬ LiesInAffineLine (E := E) (primeQuotientCoordinate P))
    (ι : Fin 3 → Fin 4) (T : Matrix (Fin 3) (Fin 3) E) (C : Fin 3 → Fin 3 → Fin 3 → E)
    (h12 : ∀ i j k, C i j k = C j i k) (h23 : ∀ i j k, C i j k = C i k j)
    (hY : ∀ j, (∑ i, genericOutputValue H E (ι i) * T i j) = 0)
    (hCY : ∀ j k, (∑ i, genericOutputValue H E (ι i) * C i j k) = -T j k)
    (hZ : matrixBilinearPairing T (fun i => Z (ι i)) (fun i => Z (ι i)) = 0)
    (hW : matrixBilinearPairing T (fun i => W (ι i)) (fun i => W (ι i)) = 0)
    (a₃ : Fin 3 → E) (S : Matrix (Fin 3) (Fin 3) E) (k₃ : E)
    (hCubic : aeval (fun i => primeQuotientCoordinate P (ι i)) (cubicFiberPolynomial a₃ S C k₃) = 0) :
    tensorTrilinearPairing C (fun i => Z (ι i)) (fun i => Z (ι i)) (fun i => Z (ι i)) = 0 ∧
      tensorTrilinearPairing C (fun i => W (ι i)) (fun i => W (ι i)) (fun i => W (ι i)) = 0 := by
  let G := FractionRing (MvPolynomial (Fin 4) E ⧸ P)
  obtain ⟨hs, ht⟩ := nonlinear_quadratic_normal_form_parameters_nonscalar
    (primeQuotientCoordinate P) (genericOutputValue H E) Z W c τ s t a α β κ q ha hx heq hline 0
  have hZc := generic_fiber_nonscalar_parameter_cubic_isotropy H hd hH hN hrank hind E P hP
    τ s t Z W c a α β κ q ha hκ hx heq hs ι T C h12 h23 hY hCY hZ a₃ S k₃ hCubic
  have hx' (i : Fin 4) : primeQuotientCoordinate P i =
      τ * algebraMap E G (genericOutputValue H E i) + t * algebraMap E G (W i) +
        s * algebraMap E G (Z i) + algebraMap E G (c i) := by rw [hx i]; ring
  have heq' : algebraMap E G q = algebraMap E G a * τ + algebraMap E G β * t +
      algebraMap E G α * s + algebraMap E G κ * t * s := by linear_combination heq
  have hWc := generic_fiber_nonscalar_parameter_cubic_isotropy H hd hH hN hrank hind E P hP
    τ t s W Z c a β α κ q ha hκ hx' heq' ht ι T C h12 h23 hY hCY hW a₃ S k₃ hCubic
  exact ⟨hZc, hWc⟩

end DimensionFourDependence
