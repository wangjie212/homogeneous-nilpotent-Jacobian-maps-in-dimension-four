import DimensionFourDependence.SegreOriginalTwoInfinityPoints
import DimensionFourDependence.SegreGeometricRulingParameter

/-! # Section 5.2: both original infinity points are finite over their own ruling parameters -/

namespace DimensionFourDependence

open MvPolynomial
attribute [local instance] MvPolynomial.gradedAlgebra

universe u
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 100000

variable {K : Type u} [Field K] [CharZero K]

/-- Section 5.2 in the original Segre coordinates: an actual nonlinear
geometric component constructs two distinct nonradial infinity points,
one on each ruling. Each point has its original normalized coordinates
over a finite extension of that ruling parameter alone, whose base is the
original rational function field. No boundary point, coefficient embedding,
primitive factorization, normal form, pole or parameter algebraicity is supplied. -/
theorem original_segre_nonlinear_geometric_fiber_has_two_finite_ruling_infinity_points
    (H : Fin 4 → MvPolynomial (Fin 4) K) {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d)
    (hN : IsNilpotent (jac H)) (hrank : polyRank (jac H) = 3) (hind : ¬ComponentsDependent H)
    (hSegre : H 0 * H 3 - H 1 * H 2 = 0)
    (E : Type u) [Field E] [IsAlgClosed E] [Algebra (polynomialOutputField H) E]
    [Algebra K E] [IsScalarTower K (polynomialOutputField H) E]
    (Q : Ideal (MvPolynomial (Fin 4) E)) [Q.IsPrime]
    (hQ : Q ∈ (extendCoefficientIdeal E (fiberVanishingIdeal
      (L := polynomialOutputField H) (rationalCoordinate (K := K) (n := 4)))).minimalPrimes)
    (hline : ¬LiesInAffineLine (E := E) (primeQuotientCoordinate Q)) :
    ∃ p r : ProjectiveSpectrum (homogeneousSubmodule (Option (Fin 4)) E),
      p ∈ projectiveClosureSet (L := E) (primeQuotientCoordinate Q) ∧
      r ∈ projectiveClosureSet (L := E) (primeQuotientCoordinate Q) ∧
      SegreFirstRulingBoundaryPoint (genericOutputValue H E 1 / genericOutputValue H E 0)
        (genericOutputValue H E 2 / genericOutputValue H E 0) p ∧
      SegreSecondRulingBoundaryPoint (genericOutputValue H E 1 / genericOutputValue H E 0)
        (genericOutputValue H E 2 / genericOutputValue H E 0) r ∧ p ≠ r ∧
      SegreFiniteRulingBoundaryPoint K (genericOutputValue H E) 2 p ∧
      SegreFiniteRulingBoundaryPoint K (genericOutputValue H E) 1 r ∧
      (∀ a : Fin 4, Nonempty (RatFunc K ≃ₐ[K]
        segreProjectiveRulingParameterField K (genericOutputValue H E) 2 p a)) ∧
      (∀ a : Fin 4, Nonempty (RatFunc K ≃ₐ[K]
        segreProjectiveRulingParameterField K (genericOutputValue H E) 1 r a)) := by
  obtain ⟨I⟩ := exists_image_relation_witness H hd hH hN
  obtain ⟨p, r, hp, hr, hpR, hrR, hpr⟩ :=
    original_segre_nonlinear_geometric_fiber_has_two_infinity_points
      H hd hH hN hrank hind E Q hQ hline hSegre
  have hpfin : SegreFiniteRulingBoundaryPoint K (genericOutputValue H E) 2 p := by
    apply geometric_segre_ruling_boundary_point_has_finite_parameter_branch
      H hd hH hN hrank hind I hSegre Q hQ 2 (by decide) p hp hpR.1
    · exact hpR.2.1
    · simpa using hpR.2.2.1
  have hrfin : SegreFiniteRulingBoundaryPoint K (genericOutputValue H E) 1 r := by
    apply geometric_segre_ruling_boundary_point_has_finite_parameter_branch
      H hd hH hN hrank hind I hSegre Q hQ 1 (by decide) r hr hrR.1
    · exact hrR.2.1
    · simpa using hrR.2.2.1
  exact ⟨p, r, hp, hr, hpR, hrR, hpr, hpfin, hrfin,
    fun a => segreProjectiveRulingParameterField_rational H hd hH hN hrank hind hSegre E Q hQ 2 (by decide) p a,
    fun a => segreProjectiveRulingParameterField_rational H hd hH hN hrank hind hSegre E Q hQ 1 (by decide) r a⟩

end DimensionFourDependence
