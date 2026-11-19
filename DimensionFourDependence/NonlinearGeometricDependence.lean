import DimensionFourDependence.QuadricCoordinateFiberExclusion
import DimensionFourDependence.DevelopableNonlinearExclusion

/-! # The nonlinear geometric generic-fiber branch of Theorem 1.1 -/

namespace DimensionFourDependence

open MvPolynomial

universe u
set_option maxHeartbeats 3500000
set_option synthInstance.maxHeartbeats 100000

variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

/-- The actual Gauss-dimension-two nonlinear branch is impossible:
Proposition 3.1 constructs the original smooth-quadric coordinates,
and the transported original Segre exclusion applies to the same component. -/
theorem original_gauss_surface_nonlinear_geometric_component_impossible
    (H : Fin 4 → MvPolynomial (Fin 4) K) {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d)
    (hN : IsNilpotent (jac H)) (hrank : polyRank (jac H) = 3)
    (hind : ¬ComponentsDependent H) (I : ImageRelationWitness H)
    (hGauss : gaussImageDimension H I = 2)
    (E : Type u) [Field E] [IsAlgClosed E] [Algebra (polynomialOutputField H) E]
    [Algebra K E] [IsScalarTower K (polynomialOutputField H) E]
    [Algebra.IsAlgebraic (polynomialOutputField H) E]
    (P : Ideal (MvPolynomial (Fin 4) E)) [P.IsPrime]
    (hP : P ∈ (extendCoefficientIdeal E (fiberVanishingIdeal
      (L := polynomialOutputField H) (rationalCoordinate (K := K) (n := 4)))).minimalPrimes)
    (hline : ¬LiesInAffineLine (E := E) (primeQuotientCoordinate P)) : False := by
  obtain ⟨_hdegree, _hsmooth, e, c, _hc, heq, _hzero⟩ :=
    proposition_3_1_over_algebraically_closed_field H hd hH hN hrank hind I hGauss P hP hline
  have hquad : aeval H (rulingPolynomialInCoordinates e) = 0 := by
    rw [heq, map_mul, aeval_C, I.vanishing, mul_zero]
  exact hline (actual_smooth_quadric_coordinates_geometric_component_lies_in_affine_line
    H hd hH hN hrank hind e hquad E P hP)

/-- The nonlinear geometric generic-fiber branch of Theorem 1.1 over
the closed original constants. The map constructs its own image witness;
the actual Gauss-image dimension exhausts the curve and surface cases.
No surface classification, coordinate normal form or auxiliary exclusion
is supplied as a hypothesis. -/
theorem nonlinear_geometric_generic_component_forces_componentsDependent
    (H : Fin 4 → MvPolynomial (Fin 4) K) {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d)
    (hN : IsNilpotent (jac H)) (hrank : polyRank (jac H) = 3)
    (E : Type u) [Field E] [IsAlgClosed E] [Algebra (polynomialOutputField H) E]
    [Algebra K E] [IsScalarTower K (polynomialOutputField H) E]
    [Algebra.IsAlgebraic (polynomialOutputField H) E]
    (P : Ideal (MvPolynomial (Fin 4) E)) [P.IsPrime]
    (hP : P ∈ (extendCoefficientIdeal E (fiberVanishingIdeal
      (L := polynomialOutputField H) (rationalCoordinate (K := K) (n := 4)))).minimalPrimes)
    (hline : ¬LiesInAffineLine (E := E) (primeQuotientCoordinate P)) : ComponentsDependent H := by
  by_contra hind
  obtain ⟨I⟩ := exists_image_relation_witness H hd hH hN
  rcases independent_gauss_image_dimension_one_or_two H hd hH hN hrank hind I with hcurve | hsurface
  · exact original_gauss_curve_nonlinear_geometric_component_impossible
      H (independent_homogeneous_nilpotent_degree_gt_one H hd hH hN hind) hH hN hrank hind I hcurve E P hP hline
  · exact original_gauss_surface_nonlinear_geometric_component_impossible
      H hd hH hN hrank hind I hsurface E P hP hline

/-- Proposition 5.1, in the stronger form supplied by the now assembled
nonlinear branch: the original image equation has degree one, so cannot
be the degree-two equation of a smooth quadric. -/
theorem proposition_5_1
    (H : Fin 4 → MvPolynomial (Fin 4) K) {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d)
    (hN : IsNilpotent (jac H)) (hrank : polyRank (jac H) = 3) (I : ImageRelationWitness H)
    (E : Type u) [Field E] [IsAlgClosed E] [Algebra (polynomialOutputField H) E]
    [Algebra K E] [IsScalarTower K (polynomialOutputField H) E]
    [Algebra.IsAlgebraic (polynomialOutputField H) E]
    (P : Ideal (MvPolynomial (Fin 4) E)) [P.IsPrime]
    (hP : P ∈ (extendCoefficientIdeal E (fiberVanishingIdeal
      (L := polynomialOutputField H) (rationalCoordinate (K := K) (n := 4)))).minimalPrimes)
    (hline : ¬LiesInAffineLine (E := E) (primeQuotientCoordinate P)) :
    ComponentsDependent H ∧ I.degree = 1 ∧ I.degree ≠ 2 := by
  have hdep := nonlinear_geometric_generic_component_forces_componentsDependent H hd hH hN hrank E P hP hline
  have hdegree := I.degree_one_of_dependent H hrank hdep
  exact ⟨hdep, hdegree, by omega⟩

end DimensionFourDependence
