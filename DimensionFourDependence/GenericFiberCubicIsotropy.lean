import DimensionFourDependence.GenericFiberSinglePoleBound
import DimensionFourDependence.SinglePoleCubicIsotropy

/-! # Cubic directions from poles of actual generic fiber parameters

The radial bounds are derived from the original nilpotent map. A pole
then gives the cubic equation over the original constants. Over
algebraically closed constants a nonscalar parameter supplies the pole.
-/

namespace DimensionFourDependence

open MvPolynomial

variable {K : Type*} [Field K] [CharZero K]

section

variable (H : Fin 4 → MvPolynomial (Fin 4) K) {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d)
    (hN : IsNilpotent (jac H)) (hrank : polyRank (jac H) = 3) (hind : ¬ ComponentsDependent H)
    (E : Type*) [Field E] [CharZero E] [Algebra (polynomialOutputField H) E]
    [Algebra K E] [IsScalarTower K (polynomialOutputField H) E]
    (P : Ideal (MvPolynomial (Fin 4) E)) [P.IsPrime]
    (hP : P ∈ (extendCoefficientIdeal E (fiberVanishingIdeal
      (L := polynomialOutputField H) (rationalCoordinate (K := K) (n := 4)))).minimalPrimes)

local notation "G" => FractionRing (MvPolynomial (Fin 4) E ⧸ P)

include hd hH hN hrank hind hP

/-- At a single isotropic-parameter pole, (3.3), the actual radial
exclusion and the cubic fiber equation give the constant cubic direction. -/
theorem generic_fiber_single_pole_cubic_isotropy (V : ValuationSubring G) [Algebra E V] :
    let vGAlgebra : Algebra V G := inferInstance
    letI : SMul V G := vGAlgebra.toSMul
    ∀ [IsScalarTower E V G] (τ s t : G) (Z W c : Fin 4 → E) (a α β κ q : E),
      a ≠ 0 → κ ≠ 0 →
      (∀ i, primeQuotientCoordinate P i = τ * algebraMap E G (genericOutputValue H E i) +
        s * algebraMap E G (Z i) + t * algebraMap E G (W i) + algebraMap E G (c i)) →
      (algebraMap E G q = algebraMap E G a * τ + algebraMap E G α * s +
        algebraMap E G β * t + algebraMap E G κ * s * t) → 1 < V.valuation s →
      ∀ (ι : Fin 3 → Fin 4) (T : Matrix (Fin 3) (Fin 3) E) (C : Fin 3 → Fin 3 → Fin 3 → E),
        (∀ i j k, C i j k = C j i k) → (∀ i j k, C i j k = C i k j) →
        (∀ j, (∑ i, genericOutputValue H E (ι i) * T i j) = 0) →
        (∀ j k, (∑ i, genericOutputValue H E (ι i) * C i j k) = -T j k) →
        matrixBilinearPairing T (fun i => Z (ι i)) (fun i => Z (ι i)) = 0 →
        ∀ (a₃ : Fin 3 → E) (S : Matrix (Fin 3) (Fin 3) E) (k₃ : E),
          aeval (fun i => primeQuotientCoordinate P (ι i)) (cubicFiberPolynomial a₃ S C k₃) = 0 →
          tensorTrilinearPairing C (fun i => Z (ι i)) (fun i => Z (ι i)) (fun i => Z (ι i)) = 0 := by
  let vGAlgebra : Algebra V G := inferInstance
  let : SMul V G := vGAlgebra.toSMul
  dsimp only
  intro hTower τ s t Z W c a α β κ q ha hκ hx heq hs ι T C h12 h23 hY hCY hZ a₃ S k₃ hCubic
  obtain ⟨ht, hτ⟩ := generic_fiber_single_pole_bounds H hd hH hN hrank hind E P hP V
    τ s t Z W c a α β κ q ha hκ hx heq hs
  exact single_pole_forces_constant_cubic_isotropy V (fun i => primeQuotientCoordinate P (ι i))
    (fun i => genericOutputValue H E (ι i)) (fun i => Z (ι i)) (fun i => W (ι i)) (fun i => c (ι i))
    τ s t (fun i => hx (ι i)) hs hτ ht T C h12 h23 hY hCY hZ a₃ S k₃ hCubic

/-- A nonscalar parameter provides its own valuation pole over
algebraically closed constants, so no valuation is an extra hypothesis. -/
theorem generic_fiber_nonscalar_parameter_cubic_isotropy [IsAlgClosed E]
    (τ s t : G) (Z W c : Fin 4 → E) (a α β κ q : E) (ha : a ≠ 0) (hκ : κ ≠ 0)
    (hx : ∀ i, primeQuotientCoordinate P i = τ * algebraMap E G (genericOutputValue H E i) +
      s * algebraMap E G (Z i) + t * algebraMap E G (W i) + algebraMap E G (c i))
    (heq : algebraMap E G q = algebraMap E G a * τ + algebraMap E G α * s +
      algebraMap E G β * t + algebraMap E G κ * s * t)
    (hs : ¬ ∃ e : E, algebraMap E G e = s)
    (ι : Fin 3 → Fin 4) (T : Matrix (Fin 3) (Fin 3) E) (C : Fin 3 → Fin 3 → Fin 3 → E)
    (h12 : ∀ i j k, C i j k = C j i k) (h23 : ∀ i j k, C i j k = C i k j)
    (hY : ∀ j, (∑ i, genericOutputValue H E (ι i) * T i j) = 0)
    (hCY : ∀ j k, (∑ i, genericOutputValue H E (ι i) * C i j k) = -T j k)
    (hZ : matrixBilinearPairing T (fun i => Z (ι i)) (fun i => Z (ι i)) = 0)
    (a₃ : Fin 3 → E) (S : Matrix (Fin 3) (Fin 3) E) (k₃ : E)
    (hCubic : aeval (fun i => primeQuotientCoordinate P (ι i)) (cubicFiberPolynomial a₃ S C k₃) = 0) :
    tensorTrilinearPairing C (fun i => Z (ι i)) (fun i => Z (ι i)) (fun i => Z (ι i)) = 0 := by
  obtain ⟨V, hV, hpole⟩ := nonscalar_has_valuation_pole s hs
  let : Algebra E V := valuationConstantAlgebra V hV
  let vGAlgebra : Algebra V G := inferInstance
  let : SMul V G := vGAlgebra.toSMul
  let : IsScalarTower E V G := valuationConstantScalarTower V hV
  exact generic_fiber_single_pole_cubic_isotropy H hd hH hN hrank hind E P hP V
    τ s t Z W c a α β κ q ha hκ hx heq hpole ι T C h12 h23 hY hCY hZ a₃ S k₃ hCubic

end

end DimensionFourDependence
