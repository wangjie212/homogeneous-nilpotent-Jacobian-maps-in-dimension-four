import DimensionFourDependence.SegreZeroPairingFiniteSquare
import DimensionFourDependence.SegreZeroPairingSourceInvariants

/-! # The original nonlinear Segre fiber constructs both zero-pairing finite ruling square factorizations -/

namespace DimensionFourDependence

open MvPolynomial
attribute [local instance] coefficientFieldScalarTower MvPolynomial.gradedAlgebra

universe u
set_option maxHeartbeats 4500000
set_option synthInstance.maxHeartbeats 100000

variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]
local notation "S₀" => FractionRing (MvPolynomial (Fin 4) K)

/-- The actual original map and nonlinear geometric component
construct the zero first invariant, nonzero actual second invariant,
its source determinant identity and two selected finite ruling square
factorizations. No q formula, nonvanishing, boundary point, stationarity,
coefficient extension or square factorization is supplied. -/
theorem original_segre_nonlinear_geometric_fiber_constructs_radial_second_finite_squares
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
      coefficientEuler _ hY q = algebraMap K _ (2 * (d : K)⁻¹ - 1) * q ∧ q ≠ 0 ∧
      algebraMap (MvPolynomial (Fin 4) K) S₀ (H 0) * (q : S₀) =
        -algebraMap (MvPolynomial (Fin 4) K) S₀ (standardRulingPolynomial (F := K)) ∧
      ∃ p r : ProjectiveSpectrum (homogeneousSubmodule (Option (Fin 4)) E),
        p ∈ projectiveClosureSet (L := E) (primeQuotientCoordinate Q) ∧
        r ∈ projectiveClosureSet (L := E) (primeQuotientCoordinate Q) ∧
        SegreFirstRulingBoundaryPoint (genericOutputValue H E 1 / genericOutputValue H E 0)
          (genericOutputValue H E 2 / genericOutputValue H E 0) p ∧
        SegreSecondRulingBoundaryPoint (genericOutputValue H E 1 / genericOutputValue H E 0)
          (genericOutputValue H E 2 / genericOutputValue H E 0) r ∧ p ≠ r ∧
        SegreFiniteRadialSecondSquareFactorization K (genericOutputValue H E)
          (genericOutputValue H E 0 * R.coefficientMap q) d 2 p ∧
        SegreFiniteRadialSecondSquareFactorization K (genericOutputValue H E)
          (genericOutputValue H E 0 * R.coefficientMap q) d 1 r := by
  obtain ⟨hY, q, k, R, hc, hq, hk, hqe⟩ :=
    original_segre_nonlinear_geometric_fiber_constructs_zero_first_invariant
      H hd hH hN hrank hind hSegre E Q hQ hline
  obtain ⟨hprod, hq0⟩ := original_segre_zero_first_invariant_second_radial_product_and_nonzero
    H hind hY q hc.symm hq
  obtain ⟨p, r, hp, hr, hpR, hrR, hpr, hpfinite, hrfinite, _hRp, _hRr⟩ :=
    original_segre_nonlinear_geometric_fiber_has_two_finite_ruling_infinity_points
      H hd hH hN hrank hind hSegre E Q hQ hline
  have htr : Algebra.trdeg K E = 3 := rank_three_output_algebraic_extension_absolute_trdeg H hrank
  refine ⟨hY, q, k, R, hc, hq, hk, hqe, hq0, hprod, p, r, hp, hr, hpR, hrR, hpr, ?_, ?_⟩
  · exact segre_realized_zero_pairing_finite_boundary_constructs_radial_second_square_factorization
      (segreOriginalOutputTriple H) hY q k (primeQuotientCoordinate Q) (genericOutputValue H E) R
      d hd hq0 hqe htr 2 (by decide) p hp hpR.1 hpR.2.1 hpR.2.2.1 hpfinite
  · exact segre_realized_zero_pairing_finite_boundary_constructs_radial_second_square_factorization
      (segreOriginalOutputTriple H) hY q k (primeQuotientCoordinate Q) (genericOutputValue H E) R
      d hd hq0 hqe htr 1 (by decide) r hr hrR.1 hrR.2.1 hrR.2.2.1 hrfinite

end DimensionFourDependence
