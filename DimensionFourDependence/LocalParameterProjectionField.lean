import DimensionFourDependence.LocalParameterFractionField
import DimensionFourDependence.PrimeLocalizationFunctionField

/-! # The projection field in the actual polynomial fraction-ring model -/

namespace DimensionFourDependence

variable {k B L : Type*} [Field k]
  [CommRing B] [IsDomain B] [IsLocalRing B] [Algebra k B]
  [Field L] [Algebra B L] [IsFractionRing B L] [Algebra k L] [IsScalarTower k B L]

/-- The actual polynomial fraction field of the projection parameter
embeds by the original local coordinate, preserving its coefficient field. -/
noncomputable def localParameterProjectionFieldHom
    (z : B) (hz0 : z ≠ 0) (hz : z ∈ IsLocalRing.maximalIdeal B) :
    FractionRing (Polynomial k) →ₐ[k] L :=
  IsLocalization.liftAlgHom (M := nonZeroDivisors (Polynomial k))
    (f := Polynomial.aeval (algebraMap B L z)) fun p => by
      apply isUnit_iff_ne_zero.mpr
      intro hp
      exact local_parameter_fraction_transcendental (k := k) (L := L) z hz0 hz
        ⟨p, mem_nonZeroDivisors_iff_ne_zero.mp p.property, hp⟩

/-- Every original polynomial retains its original coordinate value
under the actual polynomial-fraction projection embedding. -/
theorem localParameterProjectionFieldHom_polynomial
    (z : B) (hz0 : z ≠ 0) (hz : z ∈ IsLocalRing.maximalIdeal B) (p : Polynomial k) :
    localParameterProjectionFieldHom (k := k) (L := L) z hz0 hz
      (algebraMap (Polynomial k) (FractionRing (Polynomial k)) p) =
        Polynomial.aeval (algebraMap B L z) p :=
  IsLocalization.lift_eq _ _

/-- The actual polynomial-fraction projection field action. -/
@[instance_reducible]
noncomputable def localParameterProjectionFieldAlgebra
    (z : B) (hz0 : z ≠ 0) (hz : z ∈ IsLocalRing.maximalIdeal B) :
    Algebra (FractionRing (Polynomial k)) L :=
  (localParameterProjectionFieldHom (k := k) (L := L) z hz0 hz).toRingHom.toAlgebra

end DimensionFourDependence
