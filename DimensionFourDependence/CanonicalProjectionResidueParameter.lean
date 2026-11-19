import DimensionFourDependence.FiniteProjectionResidueParameter
import DimensionFourDependence.NormalizationRing

/-! # The base residue parameter on the actual canonical normalization

Every actual height-one normalization prime supplies a transcendental
residue among the two actual coordinates of its finite projection. The
finite normalization, its finite-type structure, original scalar actions
and localization center are constructed from the original affine chart.
-/

namespace DimensionFourDependence

universe u

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 2000000

variable {k A : Type u} [Field k] [CharZero k]
  [CommRing A] [IsDomain A] [Algebra k A] [Algebra.FiniteType k A]

/-- Every actual divisor prime on the canonical normalization of the
original surface chart supplies a residue-transcendental coordinate of
its finite projection. No auxiliary local ring, residue field embedding,
normalization finiteness or source-center hypothesis is supplied. -/
theorem canonical_normalization_finite_projection_transcendental_residue
    (y : Option (Fin 2) → A)
    (hfinite : Module.Finite (affineProjectionAlgebra (k := k) y) A)
    (htr : 2 ≤ Algebra.trdeg k A)
    (Q : Ideal (normalizationRing A)) [Q.IsPrime] (hQ : Q.height = 1) :
    ∃ j : Fin 2, Transcendental k
      (IsLocalRing.residue (Localization.AtPrime Q)
        (algebraMap A (Localization.AtPrime Q) (y (some j)))) := by
  let S := normalizationRing A
  let B := Localization.AtPrime Q
  let : FaithfulSMul A S := inferInstance
  let : IsScalarTower k A S := inferInstance
  let : IsScalarTower k A B := inferInstance
  let : IsScalarTower A S B := inferInstance
  let : Module.Finite A S := normalizationRing_finite A (K := k)
  let : Algebra.FiniteType k S :=
    (inferInstance : Algebra.FiniteType k A).trans (inferInstance : Algebra.FiniteType A S)
  have hcenter : ((IsLocalRing.maximalIdeal B).under S).height = 1 := by
    change ((IsLocalRing.maximalIdeal (Localization.AtPrime Q)).under (normalizationRing A)).height = 1
    rw [Localization.AtPrime.under_maximalIdeal]
    exact hQ
  exact height_one_finite_projection_has_transcendental_base_coordinate
    (k := k) (A := A) (S := S) (B := B) y hfinite htr hcenter

end DimensionFourDependence
