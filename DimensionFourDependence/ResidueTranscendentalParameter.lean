import DimensionFourDependence.Defs
import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.RingTheory.Algebraic.Defs
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.RingTheory.Localization.Basic

/-! # The parameter field inside a horizontal divisor local ring

If the parameter has transcendental residue, every nonzero polynomial in
the parameter is a unit. Hence evaluation extends to the entire rational
function field, with its original parameter value preserved.
-/

namespace DimensionFourDependence

variable {K A : Type*} [Field K] [CommRing A] [Algebra K A] [IsLocalRing A]

/-- A parameter with transcendental residue has no nonunit nonzero
polynomial values in the divisor local ring. -/
theorem parameter_polynomial_isUnit_of_residue_transcendental
    (t : A) (ht : Transcendental K (IsLocalRing.residue A t))
    (p : Polynomial K) (hp : p ≠ 0) : IsUnit (Polynomial.aeval t p) := by
  apply (IsLocalRing.residue_ne_zero_iff_isUnit _).mp
  intro hz
  apply hp
  apply transcendental_iff.mp ht p
  have hmap := Polynomial.aeval_algHom_apply
    (IsScalarTower.toAlgHom K A (IsLocalRing.ResidueField A)) t p
  exact hmap.trans hz

/-- Evaluation at a horizontal parameter extends to the whole parameter
field in the source divisor local ring. -/
noncomputable def horizontalParameterHom
    (t : A) (ht : Transcendental K (IsLocalRing.residue A t)) :
    RatFunc K →ₐ[K] A :=
  IsLocalization.liftAlgHom (S := RatFunc K) (M := nonZeroDivisors (Polynomial K))
    (f := Polynomial.aeval t) fun p =>
      parameter_polynomial_isUnit_of_residue_transcendental t ht p
        (mem_nonZeroDivisors_iff_ne_zero.mp p.property)

/-- The extended parameter field homomorphism agrees with polynomial
evaluation, so it is compatible with the original pencil parameter. -/
theorem horizontalParameterHom_polynomial
    (t : A) (ht : Transcendental K (IsLocalRing.residue A t)) (p : Polynomial K) :
    horizontalParameterHom t ht (algebraMap (Polynomial K) (RatFunc K) p) =
      Polynomial.aeval t p := by
  exact IsLocalization.lift_eq _ _

/-- The rational function variable maps to the given local parameter. -/
theorem horizontalParameterHom_X
    (t : A) (ht : Transcendental K (IsLocalRing.residue A t)) :
    horizontalParameterHom t ht RatFunc.X = t := by
  simpa using horizontalParameterHom_polynomial t ht Polynomial.X

omit [IsLocalRing A] in
/-- A rational parameter homomorphism is fixed by the image of its
variable, even when the target is a local ring rather than a field. -/
theorem rationalParameterHom_ext_X (f g : RatFunc K →ₐ[K] A)
    (hX : f RatFunc.X = g RatFunc.X) : f = g := by
  apply IsLocalization.algHom_ext (nonZeroDivisors (Polynomial K))
  apply Polynomial.algHom_ext
  exact hX

variable {F : Type*} [CommRing F] [Algebra K F] [Algebra A F] [IsScalarTower K A F]

/-- The local parameter-field embedding realizes the same rational
functions in the source field as the original pencil homomorphism. -/
theorem horizontalParameterHom_comp_source
    (t : A) (ht : Transcendental K (IsLocalRing.residue A t))
    (f : RatFunc K →ₐ[K] F) (hX : algebraMap A F t = f RatFunc.X) :
    (IsScalarTower.toAlgHom K A F).comp (horizontalParameterHom t ht) = f := by
  apply rationalParameterHom_ext_X
  change algebraMap A F (horizontalParameterHom t ht RatFunc.X) = _
  rw [horizontalParameterHom_X]
  exact hX

end DimensionFourDependence
