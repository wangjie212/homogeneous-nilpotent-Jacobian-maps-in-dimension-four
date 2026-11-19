import DimensionFourDependence.ProjectiveOutputField
import DimensionFourDependence.CurveValuationResidueAlgebraic

/-! # Actual algebraic coefficient extensions are surfaces over the Gauss parameter

Independent output coordinates give the absolute dimension of their
algebraic coefficient field and all its algebraic extensions. The actual
image of a rational parameter has dimension one. Subtracting it in the
transcendence-degree tower gives the surface bound needed in (4.4).
-/

namespace DimensionFourDependence

universe u

variable {K F : Type u} [Field K] [Field F] [Algebra K F]

/-- The image of an actual rational-parameter embedding has dimension
one over its original coefficient field. -/
theorem rational_parameter_fieldRange_trdeg_one (f : RatFunc K →ₐ[K] F) :
    Algebra.trdeg K f.fieldRange = 1 := by
  rw [rational_function_algHom_fieldRange_eq_adjoin_parameter]
  apply generatedField_singleton_trdeg_one_of_transcendental
  intro hx
  exact RatFunc.transcendental_X ((isAlgebraic_algHom_iff f f.injective).mp hx)

/-- An ambient field of dimension at most three is a surface over the
specified actual rational-parameter image. -/
theorem trdeg_over_rational_parameter_image_le_two
    (f : RatFunc K →ₐ[K] F) (htr : Algebra.trdeg K F ≤ 3) :
    Algebra.trdeg f.fieldRange F ≤ 2 := by
  have he := trdeg_add_eq (A := F) K f.fieldRange
  rw [rational_parameter_fieldRange_trdeg_one f] at he
  have hle : Algebra.trdeg f.fieldRange F + 1 ≤ (2 : Cardinal) + 1 := by
    calc
      _ = 1 + Algebra.trdeg f.fieldRange F := add_comm _ _
      _ = Algebra.trdeg K F := he
      _ ≤ 3 := htr
      _ = (2 : Cardinal) + 1 := by norm_num
  exact (Cardinal.add_one_le_add_one_iff (α := Algebra.trdeg f.fieldRange F) (β := 2)).mp hle

attribute [local instance] coefficientFieldScalarTower

/-- Algebraic closure of the actual independent output field retains
its absolute dimension over the original constants. -/
theorem independent_output_coefficientField_absolute_trdeg {n : ℕ}
    (Y : Fin n → F) (hY : AlgebraicIndependent K Y) :
    Algebra.trdeg K (coefficientField (K := K) Y) = n := by
  let E := IntermediateField.adjoin K (Set.range Y)
  have hE : Algebra.trdeg K E = n := by
    rw [← (rationalOutputEquiv Y hY).trdeg_eq, rationalSource_trdeg_eq]
  let : FaithfulSMul E (coefficientField (K := K) Y) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr
      (algebraMap E (coefficientField (K := K) Y)).injective
  have he := trdeg_add_eq (A := coefficientField (K := K) Y) K E
  rw [show Algebra.trdeg E (coefficientField (K := K) Y) = 0 from trdeg_eq_zero, add_zero, hE] at he
  exact he.symm

/-- Every actual algebraic extension of the coefficient field has
the same absolute dimension as its independent outputs. -/
theorem algebraic_coefficient_extension_absolute_trdeg {n : ℕ}
    (Y : Fin n → F) (hY : AlgebraicIndependent K Y)
    (κ : Type u) [Field κ] [Algebra (coefficientField (K := K) Y) κ]
    [Algebra K κ] [IsScalarTower K (coefficientField (K := K) Y) κ]
    [Algebra.IsAlgebraic (coefficientField (K := K) Y) κ] :
    Algebra.trdeg K κ = n := by
  let : FaithfulSMul (coefficientField (K := K) Y) κ :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr (algebraMap (coefficientField (K := K) Y) κ).injective
  let : FaithfulSMul K (coefficientField (K := K) Y) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr (algebraMap K (coefficientField (K := K) Y)).injective
  have he := trdeg_add_eq (A := κ) K (coefficientField (K := K) Y)
  rw [show Algebra.trdeg (coefficientField (K := K) Y) κ = 0 from trdeg_eq_zero, add_zero,
    independent_output_coefficientField_absolute_trdeg Y hY] at he
  exact he.symm

/-- The actual algebraic coefficient extension with three independent
outputs has relative dimension at most two over its actual Gauss parameter. -/
theorem actual_coefficient_extension_surface_over_parameter_image
    (Y : Fin 3 → F) (hY : AlgebraicIndependent K Y)
    (κ : Type u) [Field κ] [Algebra (coefficientField (K := K) Y) κ]
    [Algebra K κ] [IsScalarTower K (coefficientField (K := K) Y) κ]
    [Algebra.IsAlgebraic (coefficientField (K := K) Y) κ]
    (f : RatFunc K →ₐ[K] κ) : Algebra.trdeg f.fieldRange κ ≤ 2 :=
  trdeg_over_rational_parameter_image_le_two f (algebraic_coefficient_extension_absolute_trdeg Y hY κ).le

end DimensionFourDependence
