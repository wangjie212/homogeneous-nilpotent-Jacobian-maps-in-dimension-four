import DimensionFourDependence.ProjectiveSourceCoordinates
import DimensionFourDependence.PrimeLocalizationFunctionField
import DimensionFourDependence.SourceDivisorLocalization

/-! # Divisor local rings on the original projective source charts

These are prime localizations of the actual original-coefficient chart
algebras. Polynomial chart coordinates prove Noetherianity, and an actual
principal prime divisor gives a DVR. Its chosen fraction field is the
original projective source field, with the original coordinate inclusion.
-/

namespace DimensionFourDependence

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000

variable {K : Type*} [Field K]

/-- Every actual standard projective source coordinate algebra is
Noetherian, by its verified polynomial coordinate isomorphism. -/
theorem projective_source_chart_isNoetherianRing
    (s : Fin 4 ≃ Option (Fin 3)) :
    IsNoetherianRing (projectiveCoordinateChartAlgebra (C := K)
      (rationalCoordinate (K := K) (n := 4)) (s.symm none)) := by
  exact isNoetherianRing_of_surjective (MvPolynomial (Fin 3) K) _
    (projectiveSourceFullChartCoordinateEquiv s).toRingHom
    (projectiveSourceFullChartCoordinateEquiv s).surjective

/-- Localizing an actual original projective source chart at its
principal prime divisor constructs the projective source DVR. -/
theorem projective_source_divisor_isDVR
    (s : Fin 4 ≃ Option (Fin 3))
    (Q : Ideal (projectiveCoordinateChartAlgebra (C := K)
      (rationalCoordinate (K := K) (n := 4)) (s.symm none))) [Q.IsPrime]
    (f : projectiveCoordinateChartAlgebra (C := K)
      (rationalCoordinate (K := K) (n := 4)) (s.symm none))
    (hf : Prime f) (hQ : Q = Ideal.span {f}) :
    IsDiscreteValuationRing (Localization.AtPrime Q) := by
  let : IsNoetherianRing (projectiveCoordinateChartAlgebra (C := K)
      (rationalCoordinate (K := K) (n := 4)) (s.symm none)) := projective_source_chart_isNoetherianRing s
  exact principal_prime_localization_isDVR Q f hf hQ

/-- The actual projective source function field is also the fraction
field of each original source divisor local ring on the chosen chart. -/
theorem projective_source_divisor_isFractionRing
    (s : Fin 4 ≃ Option (Fin 3))
    (Q : Ideal (projectiveCoordinateChartAlgebra (C := K)
      (rationalCoordinate (K := K) (n := 4)) (s.symm none))) [Q.IsPrime] :
    letI : Algebra (Localization.AtPrime Q) (projectiveCoordinateChartField (C := K)
      (rationalCoordinate (K := K) (n := 4)) (s.symm none)) := primeLocalizationFractionAlgebra Q
    IsFractionRing (Localization.AtPrime Q) (projectiveCoordinateChartField (C := K)
      (rationalCoordinate (K := K) (n := 4)) (s.symm none)) :=
  primeLocalizationFraction_isFractionRing Q

end DimensionFourDependence
