import DimensionFourDependence.SegreOriginalGlobalBoundaryIncidence
import DimensionFourDependence.SegreTranscendentalRulingIncidence
import DimensionFourDependence.NilpotentProportionalLinearPower

/-! # Section 5.3: the original nonzero radial-pairing branch is impossible -/

namespace DimensionFourDependence

open MvPolynomial Matrix
attribute [local instance] coefficientFieldScalarTower MvPolynomial.gradedAlgebra

universe u
set_option maxHeartbeats 4500000
set_option synthInstance.maxHeartbeats 100000

variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]
local notation "S₀" => FractionRing (MvPolynomial (Fin 4) K)

/-- Section 5.3 in the original Segre coordinates: an actual nonlinear
geometric generic component forces the actual first invariant to vanish.
The nonzero branch constructs both selected points, their global
remainder hyperplane, its source linear root, both incidences and the
proportionality over the original constants. Differentiation constructs
the contradictory nonzero polynomial left eigenvalue. No boundary,
factorization, incidence, proportionality or eigenvalue data are supplied. -/
theorem original_segre_nonlinear_geometric_fiber_first_invariant_eq_zero
    (H : Fin 4 → MvPolynomial (Fin 4) K) {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d)
    (hN : IsNilpotent (jac H)) (hrank : polyRank (jac H) = 3) (hind : ¬ComponentsDependent H)
    (hSegre : H 0 * H 3 - H 1 * H 2 = 0)
    (E : Type u) [Field E] [IsAlgClosed E] [Algebra (polynomialOutputField H) E]
    [Algebra K E] [IsScalarTower K (polynomialOutputField H) E]
    [Algebra.IsAlgebraic (polynomialOutputField H) E]
    (Q : Ideal (MvPolynomial (Fin 4) E)) [Q.IsPrime]
    (hQ : Q ∈ (extendCoefficientIdeal E (fiberVanishingIdeal
      (L := polynomialOutputField H) (rationalCoordinate (K := K) (n := 4)))).minimalPrimes)
    (hline : ¬LiesInAffineLine (E := E) (primeQuotientCoordinate Q))
    (hY : AlgebraicIndependent K (segreOriginalOutputTriple H)) :
    firstFiberInvariantInChart (Equiv.refl (Fin 4)) (segreOriginalOutputTriple H) hY
      (segreOriginalCoefficientGraph H) = 0 := by
  obtain ⟨hY', c, hc, hbranch⟩ :=
    original_segre_nonlinear_fiber_constructs_global_remainder_and_linear_root_boundary_incidence
      H hd hH hN hrank hind hSegre E Q hQ hline
  have hc0 : c = 0 := by
    by_contra hcnz
    obtain ⟨a, b, l, ha, _hb, hl, hpower, _hvalue, _hall, p, r, _hp, _hr, hpR, hrR, _hpr,
      hpa, hra, hpl, hrl⟩ := hbranch hcnz
    have hcast1 : (1 : Fin 3).castSucc = (1 : Fin 4) := by decide
    have hcast2 : (2 : Fin 3).castSucc = (2 : Fin 4) := by decide
    have hs : Transcendental K (genericOutputValue H E 1 / genericOutputValue H E 0) := by
      simpa only [Algebra.algebraMap_self_apply, hcast1] using
        original_segre_geometric_ruling_parameter_transcendental
          H hd hH hN hrank hind hSegre E Q hQ 1 (by decide) E
    have ht : Transcendental K (genericOutputValue H E 2 / genericOutputValue H E 0) := by
      simpa only [Algebra.algebraMap_self_apply, hcast2] using
        original_segre_geometric_ruling_parameter_transcendental
          H hd hH hN hrank hind hSegre E Q hQ 2 (by decide) E
    obtain ⟨α, hα, hprop⟩ :=
      two_transcendental_segre_ruling_common_hyperplane_points_covectors_proportional
        _ _ hs ht p r hpR hrR a l ha hl hpa hra hpl hrl
    exact nilpotent_proportional_linear_power_identity_impossible H hN d hd a l hl α hα hprop hpower
  rw [← hc]
  rw [hc0]
  rfl

/-- The original map and actual nonlinear component construct the
same coefficient realization with first invariant exactly zero, retaining
the exact original second and third invariants for Section 5.4. -/
theorem original_segre_nonlinear_geometric_fiber_constructs_zero_first_invariant
    (H : Fin 4 → MvPolynomial (Fin 4) K) {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d)
    (hN : IsNilpotent (jac H)) (hrank : polyRank (jac H) = 3) (hind : ¬ComponentsDependent H)
    (hSegre : H 0 * H 3 - H 1 * H 2 = 0)
    (E : Type u) [Field E] [IsAlgClosed E] [Algebra (polynomialOutputField H) E]
    [Algebra K E] [IsScalarTower K (polynomialOutputField H) E]
    [Algebra.IsAlgebraic (polynomialOutputField H) E]
    (Q : Ideal (MvPolynomial (Fin 4) E)) [Q.IsPrime]
    (hQ : Q ∈ (extendCoefficientIdeal E (fiberVanishingIdeal
      (L := polynomialOutputField H) (rationalCoordinate (K := K) (n := 4)))).minimalPrimes)
    (hline : ¬LiesInAffineLine (E := E) (primeQuotientCoordinate Q)) :
    ∃ (hY : AlgebraicIndependent K (segreOriginalOutputTriple H))
      (q k : coefficientField (K := K) (segreOriginalOutputTriple H))
      (R : FiberCoefficientRealization (Equiv.refl (Fin 4)) (segreOriginalOutputTriple H) hY
        (segreOriginalCoefficientGraph H) 0 q k (primeQuotientCoordinate Q) (genericOutputValue H E)),
      (0 : S₀) = firstFiberInvariantInChart (Equiv.refl (Fin 4)) (segreOriginalOutputTriple H) hY
        (segreOriginalCoefficientGraph H) ∧
      (q : S₀) = secondFiberInvariant (Equiv.refl (Fin 4)) (segreOriginalOutputTriple H) hY
        (segreOriginalCoefficientGraph H) 0 ∧
      (k : S₀) = thirdFiberInvariant (Equiv.refl (Fin 4)) (segreOriginalOutputTriple H) hY
        (segreOriginalCoefficientGraph H) 0 q ∧
      coefficientEuler _ hY q = algebraMap K _ (2 * (d : K)⁻¹ - 1) * q := by
  obtain ⟨hY, c, q, k, R, hc, hq, hk, _hce, hqe, _hbranch⟩ :=
    original_segre_nonlinear_geometric_fiber_constructs_global_radial_hyperplanes
      H hd hH hN hrank hind hSegre E Q hQ hline
  have hc0 : c = 0 := by
    apply Subtype.ext
    change (c : S₀) = 0
    rw [hc]
    exact original_segre_nonlinear_geometric_fiber_first_invariant_eq_zero
      H hd hH hN hrank hind hSegre E Q hQ hline hY
  subst c
  exact ⟨hY, q, k, R, hc, hq, hk, hqe⟩

end DimensionFourDependence
