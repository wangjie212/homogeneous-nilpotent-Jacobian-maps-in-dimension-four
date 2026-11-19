import DimensionFourDependence.SegreNonlinearFiberExclusion
import DimensionFourDependence.GeometricComponentConjugacy
import DimensionFourDependence.ImageRelationConjugacy

/-! # The nonlinear smooth-quadric fiber exclusion under original linear coordinates -/

namespace DimensionFourDependence

open MvPolynomial Matrix

universe u
set_option maxHeartbeats 3500000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

/-- A determinant equation in any specified invertible original target
coordinates excludes nonlinear geometric components. The inverse source
change preserves the nilpotent Jacobian and rank, while the actual
component and its coefficient field are transported internally. -/
theorem invertible_quadric_coordinate_relation_geometric_component_lies_in_affine_line
    (H : Fin 4 → MvPolynomial (Fin 4) K) {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d)
    (hN : IsNilpotent (jac H)) (hrank : polyRank (jac H) = 3) (hind : ¬ComponentsDependent H)
    (T S : Matrix (Fin 4) (Fin 4) K) (hTS : T * S = 1) (hST : S * T = 1)
    (hquad : aeval H (linearPolynomialPullback S standardRulingPolynomial) = 0)
    (E : Type u) [Field E] [IsAlgClosed E] [Algebra (polynomialOutputField H) E]
    [Algebra K E] [IsScalarTower K (polynomialOutputField H) E]
    [Algebra.IsAlgebraic (polynomialOutputField H) E]
    (P : Ideal (MvPolynomial (Fin 4) E)) [P.IsPrime]
    (hP : P ∈ (extendCoefficientIdeal E (fiberVanishingIdeal
      (L := polynomialOutputField H) (rationalCoordinate (K := K) (n := 4)))).minimalPrimes) :
    LiesInAffineLine (E := E) (primeQuotientCoordinate P) := by
  have hH' := linearPolynomialConjugate_homogeneous T S H hH
  have hN' := linearPolynomialConjugate_nilpotent T S hTS hST H hN
  have hrank' := (linearPolynomialConjugate_polyRank T S hTS hST H).trans hrank
  have hind' := linearPolynomialConjugate_componentsIndependent T S hTS hST H hind
  have hquad' : linearPolynomialConjugate T S H 0 * linearPolynomialConjugate T S H 3 -
      linearPolynomialConjugate T S H 1 * linearPolynomialConjugate T S H 2 = 0 := by
    have he := aeval_linearPolynomialPullback_conjugate T S hTS H
      (linearPolynomialPullback S standardRulingPolynomial)
    rw [matrix_linear_polynomial_substitution_inverse S T hST, hquad] at he
    simpa only [standardRulingPolynomial, linearPolynomialPullback, map_sub, map_mul, aeval_X, map_zero] using he
  have htransport := geometric_component_transport_under_linear_conjugacy T S hTS hST H E P hP
  letI := conjugateOutputAlgebra T S hTS hST H E
  letI := conjugateOutputAlgebra_isScalarTower T S hTS hST H E
  letI := conjugateOutputAlgebra_isAlgebraic T S hTS hST H E
  obtain ⟨Q, hQ, hminimal, hback⟩ := htransport
  letI := hQ
  apply hback
  by_contra hnonlinear
  exact original_segre_nonlinear_geometric_fiber_impossible
    (linearPolynomialConjugate T S H) hd hH' hN' hrank' hind' hquad' E Q hminimal hnonlinear

/-- Proposition 5.1 for an actual smooth-quadric coordinate witness.
Every original geometric generic-fiber component is a line. -/
theorem actual_smooth_quadric_coordinates_geometric_component_lies_in_affine_line
    (H : Fin 4 → MvPolynomial (Fin 4) K) {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d)
    (hN : IsNilpotent (jac H)) (hrank : polyRank (jac H) = 3) (hind : ¬ComponentsDependent H)
    (e : (Fin 4 → K) ≃ₗ[K] ((Fin 2 → K) × (Fin 2 → K)))
    (hquad : aeval H (rulingPolynomialInCoordinates e) = 0)
    (E : Type u) [Field E] [IsAlgClosed E] [Algebra (polynomialOutputField H) E]
    [Algebra K E] [IsScalarTower K (polynomialOutputField H) E]
    [Algebra.IsAlgebraic (polynomialOutputField H) E]
    (P : Ideal (MvPolynomial (Fin 4) E)) [P.IsPrime]
    (hP : P ∈ (extendCoefficientIdeal E (fiberVanishingIdeal
      (L := polynomialOutputField H) (rationalCoordinate (K := K) (n := 4)))).minimalPrimes) :
    LiesInAffineLine (E := E) (primeQuotientCoordinate P) := by
  let g := e.trans (fourCoordinateEquiv (F := K))
  let T := LinearMap.toMatrix' g.symm.toLinearMap
  let S := LinearMap.toMatrix' g.toLinearMap
  have hTS : T * S = 1 := by
    rw [← LinearMap.toMatrix'_comp]
    have he : g.symm.toLinearMap.comp g.toLinearMap = LinearMap.id := by
      apply LinearMap.ext
      intro x
      exact g.symm_apply_apply x
    rw [he, LinearMap.toMatrix'_id]
  have hST : S * T = 1 := by
    rw [← LinearMap.toMatrix'_comp]
    have he : g.toLinearMap.comp g.symm.toLinearMap = LinearMap.id := by
      apply LinearMap.ext
      intro x
      exact g.apply_symm_apply x
    rw [he, LinearMap.toMatrix'_id]
  exact invertible_quadric_coordinate_relation_geometric_component_lies_in_affine_line
    H hd hH hN hrank hind T S hTS hST hquad E P hP

end DimensionFourDependence
