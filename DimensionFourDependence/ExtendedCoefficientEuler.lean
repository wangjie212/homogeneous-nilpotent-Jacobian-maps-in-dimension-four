import DimensionFourDependence.ExtendedCoefficientPartials
import DimensionFourDependence.CoefficientEuler

/-! # The actual output Euler derivation extends through algebraic coefficients

The already constructed extended coordinate partials identify the output
Euler derivation on every actual algebraic coefficient value. Thus all
original parameter and invariant weights hold in a boundary residue field.
-/

namespace DimensionFourDependence

variable {K : Type*} [Field K] [CharZero K]

attribute [local instance] coefficientFieldScalarTower

/-- The actual coordinate Euler derivation on an algebraic coefficient
extension restricts to the original output Euler derivation on the entire
actual coefficient field. -/
theorem extendedCoefficientEuler_extends
    (Y : Fin 3 → FractionRing (MvPolynomial (Fin 4) K)) (hY : AlgebraicIndependent K Y)
    (κ : Type*) [Field κ] [Algebra (coefficientField (K := K) Y) κ] [Algebra K κ]
    [IsScalarTower K (coefficientField (K := K) Y) κ]
    [Algebra.IsAlgebraic (coefficientField (K := K) Y) κ]
    (a : coefficientField (K := K) Y) :
    coordinateEuler (fun i => algebraMap (coefficientField (K := K) Y) κ (coefficientCoordinate (K := K) Y i))
      (extendedCoefficientPartial Y hY κ) (algebraMap (coefficientField (K := K) Y) κ a) =
      algebraMap (coefficientField (K := K) Y) κ (coefficientEuler Y hY a) := by
  simp only [coordinateEuler_apply, extendedCoefficientPartial_extends, coefficientEuler_apply, map_sum, map_mul]

end DimensionFourDependence
