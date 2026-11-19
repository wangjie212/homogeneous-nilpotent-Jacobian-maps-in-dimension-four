import DimensionFourDependence.SegreOriginalSecondSquareIdentity
import DimensionFourDependence.SegreZeroPairingNormalRelation
import DimensionFourDependence.IrreduciblePolynomialSquareRoot

/-! # Section 5.4: an original nonlinear Segre geometric fiber is impossible -/

namespace DimensionFourDependence

open MvPolynomial
attribute [local instance] coefficientFieldScalarTower MvPolynomial.gradedAlgebra

universe u
set_option maxHeartbeats 4500000
set_option synthInstance.maxHeartbeats 100000

variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

/-- Sections 5.3 and 5.4 in the original Segre coordinates. An actual
nonlinear geometric generic component constructs the zero first
invariant, the global hyperplane-square identity, the even exponent and
the nonzero determinant-power identity. The original nilpotent Jacobian
gives divergence zero, and the split Laplacian yields the contradiction.
No normal identity, square, factorization, exponent parity or differential
vanishing condition is supplied. -/
theorem original_segre_nonlinear_geometric_fiber_impossible
    (H : Fin 4 → MvPolynomial (Fin 4) K) {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d)
    (hN : IsNilpotent (jac H)) (hrank : polyRank (jac H) = 3) (hind : ¬ComponentsDependent H)
    (hSegre : H 0 * H 3 - H 1 * H 2 = 0)
    (E : Type u) [Field E] [IsAlgClosed E] [Algebra (polynomialOutputField H) E]
    [Algebra K E] [IsScalarTower K (polynomialOutputField H) E]
    [Algebra.IsAlgebraic (polynomialOutputField H) E]
    (Q : Ideal (MvPolynomial (Fin 4) E)) [Q.IsPrime]
    (hQ : Q ∈ (extendCoefficientIdeal E (fiberVanishingIdeal
      (L := polynomialOutputField H) (rationalCoordinate (K := K) (n := 4)))).minimalPrimes)
    (hline : ¬LiesInAffineLine (E := E) (primeQuotientCoordinate Q)) : False := by
  obtain ⟨γ, S, hγ, _hS, hsquare⟩ :=
    original_segre_nonlinear_geometric_fiber_constructs_source_hyperplane_square
      H hd hH hN hrank hind hSegre E Q hQ hline
  obtain ⟨I⟩ := exists_image_relation_witness H hd hH hN
  have hdet : Irreducible (standardRulingPolynomial (F := K)) :=
    original_segre_image_constructs_determinant_irreducible H hd hH hrank hind I hSegre
  obtain ⟨m, κ, hd2, hκ, hpower⟩ := scalar_irreducible_power_square_constructs_half_power
    (∑ i, S i • H i) standardRulingPolynomial hdet γ hγ d hsquare
  obtain ⟨hY, _q, _k, _R, hc, _hq, _hk, _hqe⟩ :=
    original_segre_nonlinear_geometric_fiber_constructs_zero_first_invariant
      H hd hH hN hrank hind hSegre E Q hQ hline
  have hnormal := original_segre_zero_first_invariant_constructs_polynomial_normal_relation
    H hind hSegre hY hc.symm
  have hdiv : divergence H = 0 := by rw [divergence_eq_trace]; exact trace_jac_zero H hN
  exact no_segre_normal_determinant_power_identity H m (by simpa only [hd2] using hH)
    hnormal hdiv S κ hκ hpower

end DimensionFourDependence
