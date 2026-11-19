import DimensionFourDependence.HeightOneResidueCoordinate
import DimensionFourDependence.NormalizationRing

/-! # Every canonical normalization divisor retains an original residue parameter -/

namespace DimensionFourDependence

universe u

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000

variable {E A : Type u} {σ : Type*} [Field E] [CharZero E]
  [CommRing A] [IsDomain A] [Algebra E A] [Algebra.FiniteType E A]

/-- At a height-one prime of the actual finite normalization of a
surface algebra, one of the specified original algebra generators has
transcendental residue. No independent projection or residue parameter
is supplied. -/
theorem canonical_normalization_height_one_has_transcendental_original_coordinate
    (x : σ → A) (hx : Algebra.adjoin E (Set.range x) = ⊤)
    (htr : 2 ≤ Algebra.trdeg E A)
    (Q : Ideal (normalizationRing A)) [Q.IsPrime] (hQ : Q.height = 1) :
    ∃ i, Transcendental E (IsLocalRing.residue (Localization.AtPrime Q)
      (algebraMap A (Localization.AtPrime Q) (x i))) := by
  let S := normalizationRing A
  let B := Localization.AtPrime Q
  letI : Module.Finite A S := normalizationRing_finite A (K := E)
  letI : Algebra.FiniteType E S :=
    (inferInstance : Algebra.FiniteType E A).trans (inferInstance : Algebra.FiniteType A S)
  have hc : ((IsLocalRing.maximalIdeal B).under S).height = 1 := by
    change ((IsLocalRing.maximalIdeal (Localization.AtPrime Q)).under (normalizationRing A)).height = 1
    rw [Localization.AtPrime.under_maximalIdeal]
    exact hQ
  exact height_one_integral_extension_has_transcendental_coordinate
    (k := E) (S := S) (B := B) x hx htr hc

end DimensionFourDependence
