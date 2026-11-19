import DimensionFourDependence.ProjectiveChartComponentRelations
import DimensionFourDependence.AlgebraicCompatibleSourceComponent

/-! # Actual generic-fiber components and rational boundaries through algebraic coefficient towers -/

namespace DimensionFourDependence

open MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra MvPolynomial.algebraMvPolynomial

set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Minimal component primes remain minimal over the original ideal
through a tower of algebraic coefficient extensions. Both contractions
are the original primes, so the final assertion uses the original ideal. -/
theorem minimal_components_transitive_algebraic_coefficients
    {D C A σ : Type*} [Field D] [Field C] [Field A]
    [Algebra D C] [Algebra C A] [Algebra D A] [IsScalarTower D C A]
    [Algebra.IsAlgebraic D C] [Algebra.IsAlgebraic C A]
    (I : Ideal (MvPolynomial σ D)) [I.IsPrime]
    (J : Ideal (MvPolynomial σ C))
    (hJ : J ∈ (extendCoefficientIdeal C I).minimalPrimes)
    (Q : Ideal (MvPolynomial σ A))
    (hQ : Q ∈ (extendCoefficientIdeal A J).minimalPrimes) :
    Q ∈ (extendCoefficientIdeal A I).minimalPrimes := by
  letI : J.IsPrime := hJ.isPrime
  letI : Q.IsPrime := hQ.isPrime
  have hJcontract := minimalPrime_extended_coefficients_comap C I J hJ
  have hQcontract := minimalPrime_extended_coefficients_comap A J Q hQ
  have hmap : (MvPolynomial.map (algebraMap C A) (σ := σ)).comp
      (MvPolynomial.map (algebraMap D C)) = MvPolynomial.map (algebraMap D A) := by
    apply RingHom.ext
    intro P
    change MvPolynomial.map (algebraMap C A) (MvPolynomial.map (algebraMap D C) P) = _
    rw [MvPolynomial.map_map, ← IsScalarTower.algebraMap_eq D C A]
  have hcontract : Q.comap (MvPolynomial.map (algebraMap D A)) = I := by
    calc
      _ = (Q.comap (MvPolynomial.map (algebraMap C A))).comap (MvPolynomial.map (algebraMap D C)) := by
        rw [Ideal.comap_comap, hmap]
      _ = I := by rw [hQcontract, hJcontract]
  letI : Algebra.IsAlgebraic D A := Algebra.IsAlgebraic.trans D C A
  apply prime_minimal_over_integral_extension (MvPolynomial.map (algebraMap D A)) _ I Q hcontract
  rw [← MvPolynomial.algebraMap_def]
  exact algebraMap_isIntegral_iff.mpr inferInstance

/-- A rational boundary of an actual generic-fiber component lifts
to the boundary of an actual component after any further algebraic
coefficient extension. The new coordinates retain the exact original
intermediate-field affine relations. -/
theorem rational_boundary_constructs_component_over_algebraic_coefficient_tower
    {D C A S G : Type*} [Field D] [Field C] [Field A] [Field S] [Field G]
    [Algebra D C] [Algebra C A] [Algebra D A] [IsScalarTower D C A]
    [Algebra D S] [Algebra C G]
    [Algebra.IsAlgebraic D C] [Algebra.IsAlgebraic C A] {n : ℕ}
    (x : Fin n → S) (v : Fin n → G)
    (hcomponent : fiberVanishingIdeal (L := C) v ∈
      (extendCoefficientIdeal C (fiberVanishingIdeal (L := D) x)).minimalPrimes)
    (b : Option (Fin n) → C) (hb : b ≠ 0)
    (hboundary : projectiveCoordinatePoint b hb ∈ projectiveClosureSet (L := C) v) :
    ∃ hbA : (fun j => algebraMap C A (b j)) ≠ 0,
      ∃ q : ProjectiveSpectrum (homogeneousSubmodule (Option (Fin n)) A),
        ∃ hqa : X none ∉ q.asHomogeneousIdeal,
          fiberVanishingIdeal (L := A) (fun i => projectivePrimeRatioCoordinate q none (some i)) ∈
            (extendCoefficientIdeal A (fiberVanishingIdeal (L := D) x)).minimalPrimes ∧
          (fiberVanishingIdeal (L := A) (fun i => projectivePrimeRatioCoordinate q none (some i))).comap
            (MvPolynomial.map (algebraMap C A)) = fiberVanishingIdeal (L := C) v ∧
          projectiveCoordinatePoint (fun j => algebraMap C A (b j)) hbA ∈
            projectiveClosureSet (L := A)
              (fun i => projectivePrimeRatioCoordinate q none (some i)) := by
  obtain ⟨hbA, q, hQ, hcontract, hqa, hboundaryA⟩ :=
    projective_rational_boundary_constructs_extended_affine_coordinates (A := A) v b hb hboundary
  have hnew := extended_projective_chart_coordinates_form_affine_component v q hqa hcontract
  have hnewContract := extended_projective_chart_coordinates_contract_affine_relations v q hqa hcontract
  refine ⟨hbA, q, hqa, ?_, hnewContract, hboundaryA⟩
  exact minimal_components_transitive_algebraic_coefficients _ _ hcomponent _ hnew

end DimensionFourDependence
