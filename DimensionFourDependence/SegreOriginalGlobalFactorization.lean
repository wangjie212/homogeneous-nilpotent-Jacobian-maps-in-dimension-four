import DimensionFourDependence.SegreOriginalRulingFactorizations
import DimensionFourDependence.SegreCoefficientGlobalFactorization
import DimensionFourDependence.SegreGlobalFactorizationTransport

/-! # The original nonlinear Segre fiber constructs the global constant radial hyperplanes -/

namespace DimensionFourDependence

open MvPolynomial Matrix
attribute [local instance] coefficientFieldScalarTower MvPolynomial.gradedAlgebra

universe u
set_option maxHeartbeats 4500000
set_option synthInstance.maxHeartbeats 100000

variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]
local notation "S₀" => FractionRing (MvPolynomial (Fin 4) K)

/-- The original homogeneous nilpotent rank-three independent Segre
map and an actual nonlinear geometric component construct their own
invariants and, when the first invariant is nonzero, two original
constant hyperplanes satisfying (5.3) both geometrically and in the
actual source field, with the very same covectors. No finite boundary
point, local factorization, polynomial descent, rational presentation,
global divisor factorization or hyperplane covector is supplied. -/
theorem original_segre_nonlinear_geometric_fiber_constructs_global_radial_hyperplanes
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
      (c ≠ 0 → ∃ a b : Fin 4 → K, a ≠ 0 ∧ b ≠ 0 ∧
        ((fun i => algebraMap K E (a i)) ⬝ᵥ genericOutputValue H E) ≠ 0 ∧
        ((fun i => algebraMap K E (b i)) ⬝ᵥ genericOutputValue H E) ≠ 0 ∧
        (genericOutputValue H E 0 * R.coefficientMap c) ^ d =
          ((fun i => algebraMap K E (a i)) ⬝ᵥ genericOutputValue H E) *
            ((fun i => algebraMap K E (b i)) ⬝ᵥ genericOutputValue H E) ^ d ∧
        (algebraMap (MvPolynomial (Fin 4) K) S₀ (H 0) * (c : S₀)) ^ d =
          ((fun i => algebraMap K S₀ (a i)) ⬝ᵥ
            (fun i => algebraMap (MvPolynomial (Fin 4) K) S₀ (H i))) *
          ((fun i => algebraMap K S₀ (b i)) ⬝ᵥ
            (fun i => algebraMap (MvPolynomial (Fin 4) K) S₀ (H i))) ^ d) := by
  obtain ⟨hY, c, q, k, R, hc, hq, hk, hce, hqe, p, r, _hp, _hr, _hpR, _hrR, _hpr,
      _hpfinite, _hrfinite, hbranch⟩ :=
    original_segre_geometric_fiber_constructs_nonzero_radial_pairing_ruling_factorizations
      H hd hH hN hrank hind hSegre E Q hQ hline
  refine ⟨hY, c, q, k, R, hc, hq, hk, hce, hqe, ?_⟩
  intro hc0
  obtain ⟨hpFactor, hrFactor, _hpPoly, _hrPoly, _hpCommon, _hrCommon, hpoly⟩ := hbranch hc0
  have hglobal := (hpoly inferInstance).1
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
  obtain ⟨a, b, ha, hb, haY, hbY, he⟩ :=
    segre_coefficient_embedding_constructs_global_radial_hyperplanes
      (segreOriginalOutputTriple H) hY g (genericOutputValue H E) (fun i => R.coordinate_image i)
      htr.le hySegre _ hf d hd1 p r hpFactor hrFactor hglobal
  refine ⟨a, b, ha, hb, haY, hbY, he, ?_⟩
  exact segre_realized_radial_hyperplane_power_identity_reflects_to_original_source
    H hind hSegre hY c q k (primeQuotientCoordinate Q) (genericOutputValue H E) R a b d he

end DimensionFourDependence
