import DimensionFourDependence.Defs
import Mathlib.RingTheory.Localization.AtPrime.Basic

/-! # Source-prime contraction determines the local maximal ideal

A prime lying over a source divisor also lies over the maximal ideal
after localizing the source at that divisor. This makes a given upstairs
prime eligible for the unramified source-DVR order comparison.
-/

namespace DimensionFourDependence

variable {R O B : Type*} [CommRing R] [CommRing O] [CommRing B]
  [Algebra R O] [Algebra R B] [Algebra O B] [IsScalarTower R O B]
  [IsLocalRing O]

/-- Contraction to the source divisor forces contraction to the maximal
ideal of its source local ring. No choice of an upstairs prime is made. -/
theorem source_prime_liesOver_local_maximalIdeal
    (Q : Ideal R) [Q.IsPrime] [IsLocalization.AtPrime O Q]
    (P : Ideal B) [P.LiesOver Q] : P.LiesOver (IsLocalRing.maximalIdeal O) := by
  apply (Ideal.liesOver_iff _ _).mpr
  calc
    IsLocalRing.maximalIdeal O = Q.map (algebraMap R O) :=
      (IsLocalization.AtPrime.map_eq_maximalIdeal Q O).symm
    _ = ((P.under O).under R).map (algebraMap R O) := by
      rw [Ideal.under_under, ← Ideal.over_def P Q]
    _ = P.under O := IsLocalization.map_under Q.primeCompl O _

end DimensionFourDependence
