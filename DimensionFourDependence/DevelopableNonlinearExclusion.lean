import DimensionFourDependence.CharacteristicRootNonlinearExclusion
import DimensionFourDependence.OriginalNonlinearCharacteristicRoot
import DimensionFourDependence.GaussImageSurfaceReduction

/-! # Excluding nonlinear fibers of an original nonplanar developable image -/

namespace DimensionFourDependence

open MvPolynomial

universe u

set_option quotPrecheck false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 10000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

/-- The actual original nonlinear component constructs a finite Gauss
coefficient cover and characteristic-root data; their same-branch degree
contradiction excludes the nonplanar Gauss-curve case altogether. -/
theorem original_gauss_curve_nonlinear_geometric_component_impossible
    (H : Fin 4 → MvPolynomial (Fin 4) K) {d : ℕ} (hd : 1 < d) (hH : IsHomogMap H d)
    (hN : IsNilpotent (jac H)) (hrank : polyRank (jac H) = 3)
    (hind : ¬ComponentsDependent H) (I : ImageRelationWitness H)
    (hGauss : gaussImageDimension H I = 1)
    (E : Type u) [Field E] [Algebra (polynomialOutputField H) E] [Algebra K E]
    [IsScalarTower K (polynomialOutputField H) E] [IsAlgClosed E]
    [Algebra.IsAlgebraic (polynomialOutputField H) E]
    (P : Ideal (MvPolynomial (Fin 4) E)) [P.IsPrime]
    (hP : P ∈ (extendCoefficientIdeal E (fiberVanishingIdeal
      (L := polynomialOutputField H) (rationalCoordinate (K := K) (n := 4)))).minimalPrimes)
    (hline : ¬LiesInAffineLine (E := E) (primeQuotientCoordinate P)) : False := by
  obtain ⟨e, hcover⟩ := original_nonlinear_gauss_curve_map_constructs_characteristic_root_factorization
    H I hH hind hGauss hd hN hrank E P hP hline
  obtain ⟨F, hF, aCF, hfin, hdata⟩ := hcover
  letI : Field F := hF
  letI : Algebra (closedGaussParameterField H I) F := aCF
  letI : Module.Finite (closedGaussParameterField H I) F := hfin
  letI : Algebra.IsAlgebraic (closedGaussParameterField H I) F := inferInstance
  exact actual_characteristic_root_data_exclude_nonlinear_geometric_component
    H I F hH e hd hind hGauss hN hrank hdata E P hP hline

/-- Proposition 4.1 in original component coordinates over the
algebraically closed base field used for the nonlinear-fiber argument.
A nonlinear geometric generic component and Gauss image of dimension
at most one force a constant original-field component relation. -/
theorem proposition_4_1
    (H : Fin 4 → MvPolynomial (Fin 4) K) {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d)
    (hN : IsNilpotent (jac H)) (hrank : polyRank (jac H) = 3)
    (I : ImageRelationWitness H) (hGauss : gaussImageDimension H I ≤ 1)
    (E : Type u) [Field E] [Algebra (polynomialOutputField H) E] [Algebra K E]
    [IsScalarTower K (polynomialOutputField H) E] [IsAlgClosed E]
    [Algebra.IsAlgebraic (polynomialOutputField H) E]
    (P : Ideal (MvPolynomial (Fin 4) E)) [P.IsPrime]
    (hP : P ∈ (extendCoefficientIdeal E (fiberVanishingIdeal
      (L := polynomialOutputField H) (rationalCoordinate (K := K) (n := 4)))).minimalPrimes)
    (hline : ¬LiesInAffineLine (E := E) (primeQuotientCoordinate P)) :
    ComponentsDependent H ∧ I.degree = 1 := by
  have hdep : ComponentsDependent H := by
    by_contra hind
    have hd1 := independent_homogeneous_nilpotent_degree_gt_one H hd hH hN hind
    have hcases := (Cardinal.le_one_iff.mp hGauss)
    rcases hcases with hz | ho
    · exact hind (componentsDependent_of_gauss_image_dimension_zero H hd hH I hz)
    · exact original_gauss_curve_nonlinear_geometric_component_impossible
        H hd1 hH hN hrank hind I ho E P hP hline
  exact ⟨hdep, I.degree_one_of_dependent H hrank hdep⟩

end DimensionFourDependence
