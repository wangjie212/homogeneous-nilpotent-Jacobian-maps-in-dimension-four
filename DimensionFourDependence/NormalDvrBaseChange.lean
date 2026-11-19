import DimensionFourDependence.NormalizationRing
import DimensionFourDependence.UnramifiedDvrBaseChange

/-! # Normalization does not change the horizontal divisor local models

The finite coefficient base change at a horizontal source divisor is
already normal. Its canonical normalization, and the canonical
normalization of every divisor local ring above the source DVR, are
identified with the original rings by their maps to the fraction fields.
-/

namespace DimensionFourDependence

open scoped TensorProduct

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000

variable (B : Type*) [CommRing B] [IsIntegrallyClosed B]

/-- Normalizing a normal domain in its canonical fraction field changes
neither its elements nor its base algebra structure. -/
noncomputable def normalizationOfNormalRingEquiv : normalizationRing B ≃ₐ[B] B :=
  IsIntegralClosure.equiv B (integralClosure B (FractionRing B)) (FractionRing B) B

/-- The normalization identification is the identity in the actual
canonical fraction field. -/
theorem normalizationOfNormalRingEquiv_coe (z : normalizationRing B) :
    algebraMap B (FractionRing B) (normalizationOfNormalRingEquiv B z) = (z : FractionRing B) :=
  IsIntegralClosure.algebraMap_equiv B (integralClosure B (FractionRing B)) (FractionRing B) B z

variable {k A F E : Type*} [Field k] [CharZero k] [CommRing A] [IsDomain A]
  [IsDiscreteValuationRing A] [Field F] [Field E]
  [Algebra k A] [Algebra k F] [Algebra k E] [Algebra A F]
  [IsScalarTower k A F] [FaithfulSMul A F] [Module.Finite k E]

/-- The coefficient-extended source DVR has trivial canonical
normalization, with normality derived from relative closedness. -/
noncomputable def relativelyClosedDvrBaseChangeNormalizationEquiv
    (hclosed : algebraicClosure k F = ⊥) :
    letI : IsDomain (A ⊗[k] E) := relatively_closed_local_ring_base_change_isDomain hclosed
    normalizationRing (A ⊗[k] E) ≃ₐ[A ⊗[k] E] (A ⊗[k] E) := by
  let : IsDomain (A ⊗[k] E) := relatively_closed_local_ring_base_change_isDomain hclosed
  let : IsDedekindDomain (A ⊗[k] E) := relatively_closed_dvr_base_change_dedekind hclosed
  exact normalizationOfNormalRingEquiv _

/-- No extra elements appear upon normalizing a divisor local ring of
the finite coefficient extension above the horizontal source divisor. -/
noncomputable def relativelyClosedDvrBaseChangeLocalNormalizationEquiv
    (hclosed : algebraicClosure k F = ⊥)
    (Q : Ideal (A ⊗[k] E)) [Q.IsPrime]
    [Q.LiesOver (IsLocalRing.maximalIdeal A)] :
    letI : IsDomain (A ⊗[k] E) := relatively_closed_local_ring_base_change_isDomain hclosed
    normalizationRing (Localization.AtPrime Q) ≃ₐ[Localization.AtPrime Q]
      Localization.AtPrime Q := by
  let : IsDomain (A ⊗[k] E) := relatively_closed_local_ring_base_change_isDomain hclosed
  let : IsDiscreteValuationRing (Localization.AtPrime Q) :=
    (relatively_closed_dvr_base_change_local hclosed Q).1
  exact normalizationOfNormalRingEquiv _

end DimensionFourDependence
