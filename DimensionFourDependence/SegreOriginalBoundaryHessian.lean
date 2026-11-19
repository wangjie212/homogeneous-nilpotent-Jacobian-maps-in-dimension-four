import DimensionFourDependence.SegreRealizedBoundaryHessian

/-! # The original Segre map constructs its radial-product Hessian boundary equation -/

namespace DimensionFourDependence

open MvPolynomial Matrix
attribute [local instance] coefficientFieldScalarTower MvPolynomial.gradedAlgebra

universe u
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 100000

variable {K : Type u} [Field K] [CharZero K]
local notation "S₀" => FractionRing (MvPolynomial (Fin 4) K)

/-- The original homogeneous nilpotent Segre map constructs all actual
fiber invariants and their geometric realization. Their original Euler
weights and the radial-product Hessian boundary equation hold on the
normalized coordinates of every actual infinity prime of the component. -/
theorem original_segre_geometric_fiber_constructs_radial_product_hessian_boundary_equation
    (H : Fin 4 → MvPolynomial (Fin 4) K) {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d)
    (hN : IsNilpotent (jac H)) (hrank : polyRank (jac H) = 3)
    (hind : ¬ComponentsDependent H) (hSegre : H 0 * H 3 - H 1 * H 2 = 0)
    (E : Type u) [Field E] [IsAlgClosed E] [Algebra (polynomialOutputField H) E]
    [Algebra K E] [IsScalarTower K (polynomialOutputField H) E]
    (Q : Ideal (MvPolynomial (Fin 4) E)) [Q.IsPrime]
    (hQ : Q ∈ (extendCoefficientIdeal E (fiberVanishingIdeal
      (L := polynomialOutputField H) (rationalCoordinate (K := K) (n := 4)))).minimalPrimes) :
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
      ∀ p : ProjectiveSpectrum (homogeneousSubmodule (Option (Fin 4)) E),
        p ∈ projectiveClosureSet (L := E) (primeQuotientCoordinate Q) →
        X none ∈ p.asHomogeneousIdeal →
        ∀ a : Fin 4, X (some a) ∉ p.asHomogeneousIdeal →
        matrixBilinearPairing ((coefficientHessian (segreOriginalOutputTriple H) hY
          (coefficientCoordinate (K := K) (segreOriginalOutputTriple H) 0 * c)).map
            ((algebraMap E (projectivePrimeRatioField p (some a))).comp R.coefficientMap))
              (fun i : Fin 3 => projectivePrimeRatioCoordinate p (some a) (some i.castSucc))
              (fun i : Fin 3 => projectivePrimeRatioCoordinate p (some a) (some i.castSucc)) = 0 := by
  obtain ⟨hY, c, q, k, hc, hq, hk, _he, hce, hqe⟩ :=
    exists_original_segre_weighted_fiber_invariants H hd hH hN hrank hind hSegre
  obtain ⟨R⟩ := segre_original_fiber_invariants_geometric_realization
    H hind hSegre hY c q k hc hq hk hrank E Q hQ
  refine ⟨hY, c, q, k, R, hc, hq, hk, hce, hqe, ?_⟩
  intro p hp hi a ha
  exact segre_realized_projective_prime_radial_product_hessian_zero
    (segreOriginalOutputTriple H) hY c q k (primeQuotientCoordinate Q) (genericOutputValue H E)
      R p hp hi a ha

end DimensionFourDependence
