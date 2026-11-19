import DimensionFourDependence.RadialInfinityExclusion
import DimensionFourDependence.EulerDerivation

/-! # The source Euler derivation on the rational function field -/

namespace DimensionFourDependence

open MvPolynomial

variable {K : Type*} [Field K] {n : ℕ}

/-- The ordinary source Euler vector field `sum X_i partial_i`. -/
noncomputable def sourceEuler : Derivation K (FractionRing (MvPolynomial (Fin n) K))
    (FractionRing (MvPolynomial (Fin n) K)) :=
  sourceVectorDerivation (rationalCoordinate (K := K) (n := n))

theorem sourceEuler_coordinate (i : Fin n) :
    sourceEuler (K := K) (rationalCoordinate (K := K) i) = rationalCoordinate (K := K) i :=
  sourceVectorDerivation_coordinate _ _

/-- The source Euler vector field gives the actual homogeneous polynomial degree. -/
theorem sourceEuler_homogeneous (P : MvPolynomial (Fin n) K) {d : ℕ}
    (hP : P.IsHomogeneous d) :
    sourceEuler (K := K) (algebraMap (MvPolynomial (Fin n) K)
      (FractionRing (MvPolynomial (Fin n) K)) P) =
        (d : FractionRing (MvPolynomial (Fin n) K)) * algebraMap (MvPolynomial (Fin n) K) _ P := by
  rw [sourceEuler, sourceVectorDerivation_apply]
  simp only [rationalCoordinate, rationalPartial_polynomial, ← map_mul, ← map_sum]
  rw [hP.sum_X_mul_pderiv]
  simp only [nsmul_eq_mul, map_mul, map_natCast]

end DimensionFourDependence
