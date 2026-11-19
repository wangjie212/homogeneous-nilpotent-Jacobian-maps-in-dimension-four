import DimensionFourDependence.SegreOriginalFiniteInfinityPoints
import DimensionFourDependence.SegreOriginalBoundaryHessian
import DimensionFourDependence.SegreCoefficientBivariateDescent
import DimensionFourDependence.SegreOriginalBivariateSource

/-! # Section 5.3: both original selected ruling points construct radial-product factorizations -/

namespace DimensionFourDependence

open MvPolynomial
attribute [local instance] coefficientFieldScalarTower MvPolynomial.gradedAlgebra

universe u
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 100000

variable {K : Type u} [Field K] [CharZero K]
local notation "S₀" => FractionRing (MvPolynomial (Fin 4) K)

/-- The original homogeneous nilpotent Segre map constructs its actual
invariants, geometric coefficient realization and two distinct finite
ruling infinity points. In the nonzero first-invariant branch each point
constructs its own finite ruling-wise linear-times-dth-power factorization
of the original radial pairing. Both linear factors retain the selected
point and are nonzero on the original generic output. Over closed original
constants the two ruling polynomials construct one nonzero original bivariate
polynomial with both degree bounds. No finite direction, coefficient embedding,
dimension, derivative identity, factorization or bivariate descent is supplied. -/
theorem original_segre_geometric_fiber_constructs_nonzero_radial_pairing_ruling_factorizations
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
      (c q k : coefficientField (K := K) (segreOriginalOutputTriple H))
      (R : FiberCoefficientRealization (Equiv.refl (Fin 4)) (segreOriginalOutputTriple H) hY
        (segreOriginalCoefficientGraph H) c q k (primeQuotientCoordinate Q) (genericOutputValue H E)),
      (c : S₀) = firstFiberInvariantInChart (Equiv.refl (Fin 4)) (segreOriginalOutputTriple H) hY
        (segreOriginalCoefficientGraph H) ∧
      (q : S₀) = secondFiberInvariant (Equiv.refl (Fin 4)) (segreOriginalOutputTriple H) hY
        (segreOriginalCoefficientGraph H) c ∧
      (k : S₀) = thirdFiberInvariant (Equiv.refl (Fin 4)) (segreOriginalOutputTriple H) hY
        (segreOriginalCoefficientGraph H) c q ∧
      coefficientEuler _ hY c = algebraMap K _ ((d : K)⁻¹) * c ∧
      coefficientEuler _ hY q = algebraMap K _ (2 * (d : K)⁻¹ - 1) * q ∧
      ∃ p r : ProjectiveSpectrum (homogeneousSubmodule (Option (Fin 4)) E),
        p ∈ projectiveClosureSet (L := E) (primeQuotientCoordinate Q) ∧
        r ∈ projectiveClosureSet (L := E) (primeQuotientCoordinate Q) ∧
        SegreFirstRulingBoundaryPoint (genericOutputValue H E 1 / genericOutputValue H E 0)
          (genericOutputValue H E 2 / genericOutputValue H E 0) p ∧
        SegreSecondRulingBoundaryPoint (genericOutputValue H E 1 / genericOutputValue H E 0)
          (genericOutputValue H E 2 / genericOutputValue H E 0) r ∧ p ≠ r ∧
        SegreFiniteRulingBoundaryPoint K (genericOutputValue H E) 2 p ∧
        SegreFiniteRulingBoundaryPoint K (genericOutputValue H E) 1 r ∧
        (c ≠ 0 →
          SegreFiniteRadialProductFactorization K (genericOutputValue H E)
            (genericOutputValue H E 0 * R.coefficientMap c) d 2 p ∧
          SegreFiniteRadialProductFactorization K (genericOutputValue H E)
            (genericOutputValue H E 0 * R.coefficientMap c) d 1 r ∧
          SegreBoundedNormalizedRulingPolynomial K (genericOutputValue H E)
            (genericOutputValue H E 0 * R.coefficientMap c) d 2 p ∧
          SegreBoundedNormalizedRulingPolynomial K (genericOutputValue H E)
            (genericOutputValue H E 0 * R.coefficientMap c) d 1 r ∧
          SegreAlgebraicNormalizedRulingPolynomial K (genericOutputValue H E)
            (genericOutputValue H E 0 * R.coefficientMap c) d 2 ∧
          SegreAlgebraicNormalizedRulingPolynomial K (genericOutputValue H E)
            (genericOutputValue H E 0 * R.coefficientMap c) d 1 ∧
          (IsAlgClosed K → SegreBivariateNormalizedPairingPolynomial K (genericOutputValue H E)
            (genericOutputValue H E 0 * R.coefficientMap c) d ∧
            SegreBivariateNormalizedPairingPolynomial K
              (fun i => algebraMap (MvPolynomial (Fin 4) K) S₀ (H i))
              (algebraMap (MvPolynomial (Fin 4) K) S₀ (H 0) * (c : S₀)) d)) := by
  obtain ⟨hY, c, q, k, R, hc, hq, hk, hce, hqe, _hHess⟩ :=
    original_segre_geometric_fiber_constructs_radial_product_hessian_boundary_equation
      H hd hH hN hrank hind hSegre E Q hQ
  obtain ⟨p, r, hp, hr, hpR, hrR, hpr, hpfinite, hrfinite, _hRp, _hRr⟩ :=
    original_segre_nonlinear_geometric_fiber_has_two_finite_ruling_infinity_points
      H hd hH hN hrank hind hSegre E Q hQ hline
  have htr : Algebra.trdeg K E = 3 := rank_three_output_algebraic_extension_absolute_trdeg H hrank
  refine ⟨hY, c, q, k, R, hc, hq, hk, hce, hqe, p, r, hp, hr, hpR, hrR, hpr, hpfinite, hrfinite, ?_⟩
  intro hc0
  have hpFactor : SegreFiniteRadialProductFactorization K (genericOutputValue H E)
      (genericOutputValue H E 0 * R.coefficientMap c) d 2 p := by
    apply segre_realized_finite_boundary_constructs_radial_product_factorization
      (segreOriginalOutputTriple H) hY c q k (primeQuotientCoordinate Q) (genericOutputValue H E) R
      hd hc0 hce htr 2 (by decide) p hp hpR.1 hpR.2.1
    · simpa using hpR.2.2.1
    · exact hpfinite
  have hrFactor : SegreFiniteRadialProductFactorization K (genericOutputValue H E)
      (genericOutputValue H E 0 * R.coefficientMap c) d 1 r := by
    apply segre_realized_finite_boundary_constructs_radial_product_factorization
      (segreOriginalOutputTriple H) hY c q k (primeQuotientCoordinate Q) (genericOutputValue H E) R
      hd hc0 hce htr 1 (by decide) r hr hrR.1 hrR.2.1
    · simpa using hrR.2.2.1
    · exact hrfinite
  have hy0 : genericOutputValue H E 0 ≠ 0 := by
    intro he
    have hzero : H 0 = 0 := by
      simpa only [aeval_X] using (genericOutputValue_relations H E (X 0)).mp (by
        simpa only [aeval_X] using he)
    exact (linearIndependent_of_componentsIndependent H hind).ne_zero 0 hzero
  have hpPoly := finite_segre_radial_product_factorization_constructs_normalized_polynomial
    (genericOutputValue H E) _ d 2 (by decide) hy0 p hpFactor
  have hrPoly := finite_segre_radial_product_factorization_constructs_normalized_polynomial
    (genericOutputValue H E) _ d 1 (by decide) hy0 r hrFactor
  have hpCommon := segre_normalized_ruling_polynomial_descends_to_geometric_constants
    (genericOutputValue H E) _ d 2 p hpPoly
  have hrCommon := segre_normalized_ruling_polynomial_descends_to_geometric_constants
    (genericOutputValue H E) _ d 1 r hrPoly
  refine ⟨hpFactor, hrFactor, hpPoly, hrPoly, hpCommon, hrCommon, ?_⟩
  intro hClosed
  letI : IsAlgClosed K := hClosed
  let g : coefficientField (K := K) (segreOriginalOutputTriple H) →ₐ[K] E :=
    { toRingHom := R.coefficientMap, commutes' := R.scalar_image }
  have hglobal := segre_coefficient_embedding_constructs_bivariate_normalized_pairing
    (segreOriginalOutputTriple H) hY g (genericOutputValue H E) (fun i => R.coordinate_image i)
      htr.le _ d hpCommon hrCommon
  exact ⟨hglobal, segre_realized_bivariate_pairing_identity_reflects_to_original_source H hY c q k
    (primeQuotientCoordinate Q) (genericOutputValue H E) R d hglobal⟩

end DimensionFourDependence
