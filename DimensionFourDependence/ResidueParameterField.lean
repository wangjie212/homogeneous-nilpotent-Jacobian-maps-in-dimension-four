import DimensionFourDependence.Defs
import Mathlib.FieldTheory.RatFunc.AsPolynomial

/-! # A transcendental residue supplies the whole regular parameter field

A coordinate with transcendental residue has every nonzero parameter
polynomial invertible in the actual local ring. Its full rational
function field therefore embeds there. A nonzero nonunit is then
transcendental over this regular coefficient field.
-/

namespace DimensionFourDependence

variable {k B : Type*} [Field k] [CommRing B] [IsLocalRing B] [Algebra k B]

/-- Every nonzero polynomial in a coordinate with transcendental
residue is a unit of the actual local ring. -/
theorem transcendental_residue_polynomial_isUnit
    (u : B) (hu : Transcendental k (IsLocalRing.residue B u))
    (p : Polynomial k) (hp : p ≠ 0) : IsUnit (Polynomial.aeval u p) := by
  apply (IsLocalRing.residue_ne_zero_iff_isUnit (Polynomial.aeval u p)).mp
  let f : B →ₐ[k] IsLocalRing.ResidueField B := IsScalarTower.toAlgHom k B _
  change f (Polynomial.aeval u p) ≠ 0
  rw [← Polynomial.aeval_algHom_apply f u p]
  intro h
  exact hu ⟨p, hp, h⟩

/-- The entire rational function field of the residue parameter maps
into the actual local ring through its original coordinate values. -/
noncomputable def residueParameterFieldHom
    (u : B) (hu : Transcendental k (IsLocalRing.residue B u)) : RatFunc k →ₐ[k] B :=
  IsLocalization.liftAlgHom (M := nonZeroDivisors (Polynomial k)) (f := Polynomial.aeval u) fun p =>
    transcendental_residue_polynomial_isUnit u hu p
      (mem_nonZeroDivisors_iff_ne_zero.mp p.property)

/-- The regular parameter-field map sends each actual parameter
polynomial to its specified value at the original local coordinate. -/
theorem residueParameterFieldHom_polynomial
    (u : B) (hu : Transcendental k (IsLocalRing.residue B u)) (p : Polynomial k) :
    residueParameterFieldHom u hu (algebraMap (Polynomial k) (RatFunc k) p) =
      Polynomial.aeval u p :=
  IsLocalization.lift_eq _ _

/-- A nonzero nonunit of a local domain cannot be algebraic over a
coefficient field already contained in that same actual local ring. -/
theorem local_nonzero_nonunit_transcendental [IsDomain B]
    (z : B) (hz : z ≠ 0) (hmax : z ∈ IsLocalRing.maximalIdeal B) : Transcendental k z := by
  intro h
  exact hmax (h.isIntegral.isUnit hz)

end DimensionFourDependence
