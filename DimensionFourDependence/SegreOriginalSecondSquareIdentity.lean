import DimensionFourDependence.SegreOriginalZeroPairingSquares
import DimensionFourDependence.SegreSecondSquareCoefficientIdentity
import DimensionFourDependence.SegreSecondSquareSourceTransport

/-! # The original nonlinear Segre fiber constructs equation (5.4) -/

namespace DimensionFourDependence

open MvPolynomial Matrix
attribute [local instance] coefficientFieldScalarTower MvPolynomial.gradedAlgebra

universe u
set_option maxHeartbeats 4500000
set_option synthInstance.maxHeartbeats 100000

variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]
local notation "R₀" => MvPolynomial (Fin 4) K
local notation "S₀" => FractionRing (MvPolynomial (Fin 4) K)

/-- Equation (5.4), constructed from the original map and an actual
nonlinear geometric fiber. The actual invariants, zero first invariant,
nonzero second invariant, finite ruling squares, common-field polynomial,
global square factorization and original source reflection are derived.
No square identity, hyperplane, scalar or divisor decomposition is supplied. -/
theorem original_segre_nonlinear_geometric_fiber_constructs_source_hyperplane_square
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
    ∃ (γ : K) (S : Fin 4 → K), γ ≠ 0 ∧ S ≠ 0 ∧
      (∑ i, S i • H i) ^ 2 = MvPolynomial.C γ * standardRulingPolynomial ^ d := by
  obtain ⟨hY, q, k, R, _hc, _hq, _hk, _hqe, hq0, hprod,
      p, r, _hp, _hr, _hpR, _hrR, _hpr, hpFactor, hrFactor⟩ :=
    original_segre_nonlinear_geometric_fiber_constructs_radial_second_finite_squares
      H hd hH hN hrank hind hSegre E Q hQ hline
  have htr : Algebra.trdeg K E = 3 := rank_three_output_algebraic_extension_absolute_trdeg H hrank
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
  have hf : genericOutputValue H E 0 * R.coefficientMap q ≠ 0 :=
    mul_ne_zero hy0 ((map_ne_zero R.coefficientMap).mpr hq0)
  let g : coefficientField (K := K) (segreOriginalOutputTriple H) →ₐ[K] E :=
    { toRingHom := R.coefficientMap, commutes' := R.scalar_image }
  obtain ⟨γ, S, hγ, hS, _hSY, he⟩ :=
    segre_coefficient_embedding_constructs_global_radial_second_hyperplane_square
      (segreOriginalOutputTriple H) hY g (genericOutputValue H E) (fun i => R.coordinate_image i)
      htr.le hySegre _ hf d p r hpFactor hrFactor
  have hsource := segre_realized_radial_second_square_reflects_to_original_source
    H hind hSegre hY q k (primeQuotientCoordinate Q) (genericOutputValue H E) R γ S d he
  rw [hprod] at hsource
  have hmap : algebraMap R₀ S₀ (∑ i, S i • H i) =
      ((fun i => algebraMap K S₀ (S i)) ⬝ᵥ (fun i => algebraMap R₀ S₀ (H i))) := by
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [smul_eq_C_mul]
    change algebraMap R₀ S₀ (MvPolynomial.C (S i) * H i) = _
    rw [map_mul]
    rfl
  have hpolynomial : (-standardRulingPolynomial (F := K)) ^ d =
      MvPolynomial.C γ * (∑ i, S i • H i) ^ 2 := by
    apply IsFractionRing.injective R₀ S₀
    simp only [map_pow, map_neg, map_mul, hmap]
    exact hsource
  refine ⟨γ⁻¹ * (-1) ^ d, S, mul_ne_zero (inv_ne_zero hγ) (pow_ne_zero d (neg_ne_zero.mpr one_ne_zero)), hS, ?_⟩
  have hunit : MvPolynomial.C γ⁻¹ * MvPolynomial.C γ = (1 : R₀) := by
    rw [← map_mul, inv_mul_cancel₀ hγ, map_one]
  calc
    (∑ i, S i • H i) ^ 2 = MvPolynomial.C γ⁻¹ * (-standardRulingPolynomial (F := K)) ^ d := by
      rw [hpolynomial, ← mul_assoc, hunit, one_mul]
    _ = _ := by
      rw [neg_eq_neg_one_mul, mul_pow, map_mul, map_pow, map_neg, map_one]
      ring

end DimensionFourDependence
