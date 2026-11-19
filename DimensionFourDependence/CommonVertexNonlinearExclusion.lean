import DimensionFourDependence.GeometricComponentConjugacy
import DimensionFourDependence.GaussDimensionConjugacy
import DimensionFourDependence.OriginalFixedVertexNonlinearExclusion

/-! # A constant common vertex excludes nonlinear geometric generic components -/

namespace DimensionFourDependence

open MvPolynomial Matrix

universe u

set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]
    (H : Fin 4 → MvPolynomial (Fin 4) K) {d : ℕ} (hd : 1 < d) (hH : IsHomogMap H d)
    (hN : IsNilpotent (jac H)) (hrank : polyRank (jac H) = 3)
    (hind : ¬ComponentsDependent H) (I : ImageRelationWitness H)
    (hGauss : gaussImageDimension H I = 1)
    (v : Fin 4 → K) (hv : v ≠ 0)
    (hnormal : rationalImageNormal H I.equation ⬝ᵥ
      (fun i => algebraMap K (FractionRing (MvPolynomial (Fin 4) K)) (v i)) = 0)
    (E : Type u) [Field E] [Algebra (polynomialOutputField H) E] [Algebra K E]
    [IsScalarTower K (polynomialOutputField H) E] [IsAlgClosed E]
    [Algebra.IsAlgebraic (polynomialOutputField H) E]
    (P : Ideal (MvPolynomial (Fin 4) E)) [P.IsPrime]
    (hP : P ∈ (extendCoefficientIdeal E (fiberVanishingIdeal
      (L := polynomialOutputField H) (rationalCoordinate (K := K) (n := 4)))).minimalPrimes)

include hd hH hN hrank hind hGauss hv hnormal hP

/-- Every actual geometric generic-fiber component is a line when the
Gauss curve has a nonzero constant common vertex. The coordinate matrices,
transported constants, image witness and component are all constructed. -/
theorem original_common_vertex_map_geometric_component_lies_in_affine_line :
    LiesInAffineLine (E := E) (primeQuotientCoordinate P) := by
  obtain ⟨T, S, hTS, hST, J, hH', hN', hrank', hind', hGauss', haxis⟩ :=
    common_vertex_constructs_standard_axis_map_data H I hH hN hrank hind v hv hnormal
  have htransport := geometric_component_transport_under_linear_conjugacy T S hTS hST H E P hP
  letI := conjugateOutputAlgebra T S hTS hST H E
  letI := conjugateOutputAlgebra_isScalarTower T S hTS hST H E
  letI := conjugateOutputAlgebra_isAlgebraic T S hTS hST H E
  obtain ⟨Q, hQ, hminimal, hback⟩ := htransport
  letI := hQ
  apply hback
  exact original_fixed_vertex_map_geometric_component_lies_in_affine_line
    (linearPolynomialConjugate T S H) hd hH' hN' hrank' hind' J (hGauss'.trans hGauss)
    haxis E Q hminimal

/-- The same original-map hypotheses exclude every actual nonlinear
component, without fixing the common vertex to a chosen coordinate axis. -/
theorem original_common_vertex_map_has_no_nonlinear_geometric_component
    (hline : ¬LiesInAffineLine (E := E) (primeQuotientCoordinate P)) : False :=
  hline (original_common_vertex_map_geometric_component_lies_in_affine_line
    H hd hH hN hrank hind I hGauss v hv hnormal E P hP)

omit hind in
/-- The constant-vertex branch of the Gauss-dimension-one argument
forces dependence as soon as an actual nonlinear component is present. -/
theorem componentsDependent_of_common_vertex_and_nonlinear_geometric_component
    (hline : ¬LiesInAffineLine (E := E) (primeQuotientCoordinate P)) :
    ComponentsDependent H := by
  classical
  by_contra hind'
  exact original_common_vertex_map_has_no_nonlinear_geometric_component
    H hd hH hN hrank hind' I hGauss v hv hnormal E P hP hline

end DimensionFourDependence
