import DimensionFourDependence.ResidueParameterField

/-! # The actual rational projection field of a vanishing local coordinate

The original coordinate defines the rational parameter inside the
specified target fraction field. Injectivity follows from its being a
nonzero nonunit over the regular coefficient field in the local ring.
-/

namespace DimensionFourDependence

variable {k B L : Type*} [Field k]
  [CommRing B] [IsDomain B] [IsLocalRing B] [Algebra k B]
  [Field L] [Algebra B L] [IsFractionRing B L] [Algebra k L] [IsScalarTower k B L]

/-- The actual vanishing local coordinate is transcendental in the
specified fraction field over the regular coefficient field. -/
theorem local_parameter_fraction_transcendental
    (z : B) (hz0 : z ≠ 0) (hz : z ∈ IsLocalRing.maximalIdeal B) :
    Transcendental k (algebraMap B L z) :=
  (transcendental_algebraMap_iff (IsFractionRing.injective B L)).mpr
    (local_nonzero_nonunit_transcendental (k := k) z hz0 hz)

/-- The actual projection parameter induces the specified rational
function field embedding, retaining the original coefficient field. -/
noncomputable def localParameterFractionHom
    (z : B) (hz0 : z ≠ 0) (hz : z ∈ IsLocalRing.maximalIdeal B) : RatFunc k →ₐ[k] L :=
  IsLocalization.liftAlgHom (M := nonZeroDivisors (Polynomial k))
    (f := Polynomial.aeval (algebraMap B L z)) fun p => by
      apply isUnit_iff_ne_zero.mpr
      intro hp
      exact local_parameter_fraction_transcendental (k := k) (L := L) z hz0 hz
        ⟨p, mem_nonZeroDivisors_iff_ne_zero.mp p.property, hp⟩

/-- The original parameter polynomial retains its actual value in
the target fraction field. -/
theorem localParameterFractionHom_polynomial
    (z : B) (hz0 : z ≠ 0) (hz : z ∈ IsLocalRing.maximalIdeal B) (p : Polynomial k) :
    localParameterFractionHom (k := k) (L := L) z hz0 hz
      (algebraMap (Polynomial k) (RatFunc k) p) = Polynomial.aeval (algebraMap B L z) p :=
  IsLocalization.lift_eq _ _

/-- The rational variable maps to the same original vanishing
coordinate in the actual fraction field. -/
theorem localParameterFractionHom_X
    (z : B) (hz0 : z ≠ 0) (hz : z ∈ IsLocalRing.maximalIdeal B) :
    localParameterFractionHom (k := k) (L := L) z hz0 hz RatFunc.X = algebraMap B L z := by
  rw [← RatFunc.algebraMap_X, localParameterFractionHom_polynomial, Polynomial.aeval_X]

/-- The actual projection field action used in the multiplicity bound. -/
@[instance_reducible]
noncomputable def localParameterFractionAlgebra
    (z : B) (hz0 : z ≠ 0) (hz : z ∈ IsLocalRing.maximalIdeal B) : Algebra (RatFunc k) L :=
  (localParameterFractionHom (k := k) (L := L) z hz0 hz).toRingHom.toAlgebra

end DimensionFourDependence
