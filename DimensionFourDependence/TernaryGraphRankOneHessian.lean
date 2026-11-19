import DimensionFourDependence.BinaryOutputPartialConstants
import DimensionFourDependence.ClosedFieldCoefficientPartials
import DimensionFourDependence.TernaryGraphPlaneDifferentiation

/-! # The second zero Hessian column supplies an algebraically dependent pair -/

namespace DimensionFourDependence

open MvPolynomial

universe u
set_option maxHeartbeats 1600000

variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]
local notation "F" => FractionRing (MvPolynomial (Fin 3) K)

/-- When the second Hessian column vanishes, subtracting an original
constant multiple of the second output makes the last output
algebraic over the first one. -/
theorem ternary_graph_zero_second_hessian_column_constructs_algebraic_output_pair
    (Y : Fin 2 → F) (hY : AlgebraicIndependent K Y) (w : coefficientField (K := K) Y)
    (hz : ∀ i, ternaryGraphHessian Y hY w i 1 = 0) :
    ∃ μ : K, IsAlgebraic (IntermediateField.adjoin K {Y 0})
      ((w : F) - algebraMap K F μ * Y 1) := by
  let L := coefficientField (K := K) Y
  let : IsScalarTower K L F := coefficientFieldScalarTower Y
  let D := coefficientPartial Y hY 1
  obtain ⟨μ, hμ⟩ := closed_field_coefficientPartials_common_constant_is_scalar Y hY (D w) (by
    intro i
    apply Subtype.ext
    exact hz i)
  let v := coefficientCoordinate (K := K) Y 1
  let a : L := w - algebraMap K L μ * v
  have hcoord : D v = if (1 : Fin 2) = 1 then 1 else 0 := coefficientPartial_coordinate Y hY 1 1
  have hv : D v = 1 := hcoord.trans (by simp)
  have hD : D a = 0 := by
    change D (w - algebraMap K L μ * v) = 0
    rw [map_sub, D.leibniz, D.map_algebraMap, hv, smul_zero, add_zero, smul_eq_mul, mul_one]
    exact sub_eq_zero.mpr hμ.symm
  refine ⟨μ, ?_⟩
  have he := second_coefficientPartial_zero_isAlgebraic_over_first_output Y hY a hD
  change IsAlgebraic (IntermediateField.adjoin K {Y 0})
    (algebraMap L F (w - algebraMap K L μ * v)) at he
  simpa only [map_sub, map_mul, ← IsScalarTower.algebraMap_apply K L F,
    IntermediateField.algebraMap_apply, v, coefficientCoordinate_coe] using he

end DimensionFourDependence
