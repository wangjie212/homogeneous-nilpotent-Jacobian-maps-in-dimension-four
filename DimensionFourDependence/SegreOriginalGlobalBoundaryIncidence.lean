import DimensionFourDependence.SegreOriginalGlobalFactorization
import DimensionFourDependence.SegreCoefficientSelectedRemainder
import DimensionFourDependence.LinearPowerFiberInfinity

/-! # The original two selected ruling points lie on both fixed source hyperplanes -/

namespace DimensionFourDependence

open MvPolynomial Matrix
attribute [local instance] coefficientFieldScalarTower MvPolynomial.gradedAlgebra

universe u
set_option maxHeartbeats 5000000
set_option synthInstance.maxHeartbeats 100000

variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]
local notation "R₀" => MvPolynomial (Fin 4) K
local notation "S₀" => FractionRing (MvPolynomial (Fin 4) K)

/-- The actual original nonlinear Segre fiber constructs its invariant
and, in the nonzero branch, the global remainder hyperplane, source linear
root and two distinct selected infinity points on both hyperplanes. The
source linear form vanishes at every infinity point of the actual fiber.
No selected points, global factors, source linear form or incidence
assumptions are supplied. All covectors are over the original constants. -/
theorem original_segre_nonlinear_fiber_constructs_global_remainder_and_linear_root_boundary_incidence
    (H : Fin 4 → R₀) {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d)
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
      (c : coefficientField (K := K) (segreOriginalOutputTriple H)),
      (c : S₀) = firstFiberInvariantInChart (Equiv.refl (Fin 4)) (segreOriginalOutputTriple H) hY
        (segreOriginalCoefficientGraph H) ∧
      (c ≠ 0 → ∃ a b l : Fin 4 → K, a ≠ 0 ∧ b ≠ 0 ∧ l ≠ 0 ∧
        linearFormPolynomial l ^ d = outputLinearCombination H a ∧
        algebraMap R₀ S₀ (linearFormPolynomial l) =
          (algebraMap R₀ S₀ (H 0) * (c : S₀)) /
            ((fun i => algebraMap K S₀ (b i)) ⬝ᵥ (fun i => algebraMap R₀ S₀ (H i))) ∧
        (∀ z : ProjectiveSpectrum (homogeneousSubmodule (Option (Fin 4)) E),
          z ∈ projectiveClosureSet (L := E) (primeQuotientCoordinate Q) →
          X none ∈ z.asHomogeneousIdeal →
          rename some (linearFormPolynomial (fun i => algebraMap K E (l i))) ∈ z.asHomogeneousIdeal) ∧
        ∃ p r : ProjectiveSpectrum (homogeneousSubmodule (Option (Fin 4)) E),
          p ∈ projectiveClosureSet (L := E) (primeQuotientCoordinate Q) ∧
          r ∈ projectiveClosureSet (L := E) (primeQuotientCoordinate Q) ∧
          SegreFirstRulingBoundaryPoint (genericOutputValue H E 1 / genericOutputValue H E 0)
            (genericOutputValue H E 2 / genericOutputValue H E 0) p ∧
          SegreSecondRulingBoundaryPoint (genericOutputValue H E 1 / genericOutputValue H E 0)
            (genericOutputValue H E 2 / genericOutputValue H E 0) r ∧ p ≠ r ∧
          rename some (linearFormPolynomial (fun i => algebraMap K E (a i))) ∈ p.asHomogeneousIdeal ∧
          rename some (linearFormPolynomial (fun i => algebraMap K E (a i))) ∈ r.asHomogeneousIdeal ∧
          rename some (linearFormPolynomial (fun i => algebraMap K E (l i))) ∈ p.asHomogeneousIdeal ∧
          rename some (linearFormPolynomial (fun i => algebraMap K E (l i))) ∈ r.asHomogeneousIdeal) := by
  obtain ⟨hY, c, q, k, R, hc, _hq, _hk, _hce, _hqe, p, r, hp, hr, hpR, hrR, hpr,
      _hpfinite, _hrfinite, hbranch⟩ :=
    original_segre_geometric_fiber_constructs_nonzero_radial_pairing_ruling_factorizations
      H hd hH hN hrank hind hSegre E Q hQ hline
  refine ⟨hY, c, hc, ?_⟩
  intro hc0
  obtain ⟨hpFactor, hrFactor, _hpPoly, _hrPoly, _hpCommon, _hrCommon, hpoly⟩ := hbranch hc0
  have hglobalPoly := (hpoly inferInstance).1
  have htr : Algebra.trdeg K E = 3 := rank_three_output_algebraic_extension_absolute_trdeg H hrank
  have hd1 : 1 < d := independent_nilpotent_homogeneous_degree_greater_than_one H hd hH hN hind
  have hy0 : genericOutputValue H E 0 ≠ 0 := by
    intro he
    have hzero : H 0 = 0 := by
      simpa only [aeval_X] using (genericOutputValue_relations H E (X 0)).mp (by
        simpa only [aeval_X] using he)
    exact (linearIndependent_of_componentsIndependent H hind).ne_zero 0 hzero
  have hySegre : genericOutputValue H E 0 * genericOutputValue H E 3 -
      genericOutputValue H E 1 * genericOutputValue H E 2 = 0 := by
    have he := (genericOutputValue_relations H E (X 0 * X 3 - X 1 * X 2)).mpr (by
      simpa only [map_sub, map_mul, aeval_X] using hSegre)
    simpa only [map_sub, map_mul, aeval_X] using he
  have hf : genericOutputValue H E 0 * R.coefficientMap c ≠ 0 :=
    mul_ne_zero hy0 ((map_ne_zero R.coefficientMap).mpr hc0)
  let g : coefficientField (K := K) (segreOriginalOutputTriple H) →ₐ[K] E :=
    { toRingHom := R.coefficientMap, commutes' := R.scalar_image }
  obtain ⟨a, b, ha, hb, _haY, _hbY, he⟩ :=
    segre_coefficient_embedding_constructs_global_radial_hyperplanes
      (segreOriginalOutputTriple H) hY g (genericOutputValue H E) (fun i => R.coordinate_image i)
      htr.le hySegre _ hf d hd1 p r hpFactor hrFactor hglobalPoly
  have hpa := segre_coefficient_embedding_selected_point_mem_global_remainder_hyperplane
    (segreOriginalOutputTriple H) hY g (genericOutputValue H E) (fun i => R.coordinate_image i)
      htr.le hySegre _ hf d hd1 2 (by decide) p hpR.2.1 hpR.2.2.1 hpFactor a b he
  have hra := segre_coefficient_embedding_selected_point_mem_global_remainder_hyperplane
    (segreOriginalOutputTriple H) hY g (genericOutputValue H E) (fun i => R.coordinate_image i)
      htr.le hySegre _ hf d hd1 1 (by decide) r hrR.2.1 hrR.2.2.1 hrFactor a b he
  have heSource := segre_realized_radial_hyperplane_power_identity_reflects_to_original_source
    H hind hSegre hY c q k (primeQuotientCoordinate Q) (genericOutputValue H E) R a b d he
  have hcSource : (c : S₀) ≠ 0 :=
    (map_ne_zero (algebraMap (coefficientField (K := K) (segreOriginalOutputTriple H)) S₀)).mpr hc0
  have hfSource : algebraMap R₀ S₀ (H 0) * (c : S₀) ≠ 0 :=
    mul_ne_zero (original_segre_first_output_ne_zero H hind) hcSource
  obtain ⟨l, hl, hvalue, hpower⟩ := segre_global_radial_hyperplane_identity_constructs_source_linear_root
    H hd hH hind _ hfSource a b hb heSource
  have houtput (i : Fin 4) : aeval (primeQuotientCoordinate Q) (H i) =
      algebraMap E (FractionRing (MvPolynomial (Fin 4) E ⧸ Q)) (genericOutputValue H E i) := by
    simpa only [aeval_map_coefficients] using geometric_component_generic_output_evaluation H E Q hQ i
  have hall (z : ProjectiveSpectrum (homogeneousSubmodule (Option (Fin 4)) E))
      (hz : z ∈ projectiveClosureSet (L := E) (primeQuotientCoordinate Q))
      (hinfty : X none ∈ z.asHomogeneousIdeal) :
      rename some (linearFormPolynomial (fun i => algebraMap K E (l i))) ∈ z.asHomogeneousIdeal :=
    original_linear_power_output_identity_all_fiber_infinity_points H l a d hd hpower
      (primeQuotientCoordinate Q) (genericOutputValue H E) houtput z hz hinfty
  exact ⟨a, b, l, ha, hb, hl, hpower, hvalue, hall, p, r, hp, hr, hpR, hrR, hpr,
    hpa, hra, hall p hp hpR.1, hall r hr hrR.1⟩

end DimensionFourDependence
