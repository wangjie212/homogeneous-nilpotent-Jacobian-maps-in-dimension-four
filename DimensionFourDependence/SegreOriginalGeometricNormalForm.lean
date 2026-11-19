import DimensionFourDependence.SegreRealizedFiberNormalForm
import DimensionFourDependence.ZeroInvariantGeometricFiber

/-! # Original nonlinear geometric fibers construct the exact Segre normal form -/

namespace DimensionFourDependence

open MvPolynomial

set_option maxHeartbeats 3000000

variable {K : Type*} [Field K] [CharZero K]

/-- The original homogeneous nilpotent Segre map constructs the full
canonical normal form on every actual nonlinear geometric generic
component. All coefficient invariants, their Euler weight, the fixed
output chart, and the compatible geometric realization are derived.
Nonlinearity also excludes simultaneous vanishing of `c` and `q`. -/
theorem original_segre_geometric_fiber_constructs_radial_transverse_normal_form
    (H : Fin 4 → MvPolynomial (Fin 4) K) {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d)
    (hN : IsNilpotent (jac H)) (hrank : polyRank (jac H) = 3)
    (hind : ¬ComponentsDependent H) (hSegre : H 0 * H 3 - H 1 * H 2 = 0)
    (E : Type*) [Field E] [IsAlgClosed E] [Algebra (polynomialOutputField H) E]
    [Algebra K E] [IsScalarTower K (polynomialOutputField H) E]
    (P : Ideal (MvPolynomial (Fin 4) E)) [P.IsPrime]
    (hP : P ∈ (extendCoefficientIdeal E (fiberVanishingIdeal
      (L := polynomialOutputField H) (rationalCoordinate (K := K) (n := 4)))).minimalPrimes)
    (hline : ¬LiesInAffineLine (E := E) (primeQuotientCoordinate P)) :
    let G := FractionRing (MvPolynomial (Fin 4) E ⧸ P)
    let x := primeQuotientCoordinate P
    let y := genericOutputValue H E
    y 0 ≠ 0 ∧ ∃ (c q α β : E) (τ v w : G),
      (c ≠ 0 ∨ q ≠ 0) ∧
      (c = 0 → α = 0 ∧ β = 0) ∧
      (∀ i, x i = τ * algebraMap E G (y i) +
        v * algebraMap E G (segreFirstRulingDirection (y 2 / y 0) i) +
        w * algebraMap E G (segreSecondRulingDirection (y 1 / y 0) i) +
        algebraMap E G ((Pi.single 3 c : Fin 4 → E) i)) ∧
      algebraMap E G q = algebraMap E G (algebraMap K E ((d : K)⁻¹) * c) * τ +
        algebraMap E G α * v + algebraMap E G β * w + algebraMap E G (1 / y 0) * v * w := by
  let G := FractionRing (MvPolynomial (Fin 4) E ⧸ P)
  let x := primeQuotientCoordinate P
  let y := genericOutputValue H E
  obtain ⟨hY, c, q, k, hc, hq, hk, _hhE, hcE, _hqE⟩ :=
    exists_original_segre_weighted_fiber_invariants H hd hH hN hrank hind hSegre
  let W := segreOriginalFiberEquationWitness H hind hSegre hY c q k hc hq hk
  obtain ⟨R⟩ := segre_original_fiber_invariants_geometric_realization H hind hSegre hY c q k hc hq hk hrank E P hP
  obtain ⟨hy0, τ, v, w, hx, heq⟩ := segre_realized_fiber_constructs_radial_transverse_normal_form
    (segreOriginalOutputTriple H) hY c q k x y R ((d : K)⁻¹) hcE
  have hn := nonlinear_geometric_component_invariants_nonzero H hd hH hN hrank W
    (segreOriginalCoefficientGraph H) c q (segre_original_coefficient_graph_value H hind hSegre)
    hc hq E P hP hline
  refine ⟨hy0, R.coefficientMap c, R.coefficientMap q,
    R.coefficientMap (coefficientPartial _ hY 1 c), R.coefficientMap (coefficientPartial _ hY 2 c),
    τ, v, w, ?_, ?_, hx, heq⟩
  · rcases hn with hc0 | hq0
    · left
      exact (map_ne_zero R.coefficientMap).mpr hc0
    · right
      exact (map_ne_zero R.coefficientMap).mpr hq0
  · intro he
    have hc0 : c = 0 := R.coefficientMap.injective (by simpa only [map_zero] using he)
    simp only [hc0, map_zero, and_self]

end DimensionFourDependence
