import DimensionFourDependence.PencilCoefficientCurveField
import DimensionFourDependence.CoefficientRestrictionCurveResidue
import DimensionFourDependence.LocalPencilZero

/-! # A local pencil zero constructs its own coefficient curve and algebraic residue -/

namespace DimensionFourDependence

universe u

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000

variable {E A F : Type u} [Field E] [CommRing A] [IsDomain A] [ValuationRing A]
  [Field F] [Algebra E A] [Algebra A F] [IsFractionRing A F]
  [Algebra E F] [IsScalarTower E A F]

/-- A nonzero regular pencil zero supplies transcendence, curve
dimension, a nontrivial restricted valuation and an algebraic residue
field for the full relative coefficient closure, all at the same source valuation. -/
theorem regular_pencil_coefficient_curve_residue_isAlgebraic
    (t : F) (f : A) (hf : f ≠ 0) (hzero : f ∈ IsLocalRing.maximalIdeal A)
    (hvalue : algebraMap A F f = t) :
    let C := pencilCoefficientCurveField (E := E) t
    letI := pencilCoefficientCurveField_scalarTower (E := E) t
    letI := coefficientRestrictionConstantAlgebra (A := A) (F := F) C E
    Algebra.IsAlgebraic E (IsLocalRing.ResidueField
      (coefficientRestrictionValuationSubring (A := A) (F := F) C)) := by
  let C := pencilCoefficientCurveField (E := E) t
  letI := pencilCoefficientCurveField_scalarTower (E := E) t
  letI := coefficientRestrictionConstantAlgebra (A := A) (F := F) C E
  have ht : Transcendental E t := by
    rw [← hvalue]
    exact (transcendental_algebraMap_iff (IsFractionRing.injective A F)).mpr
      (local_nonzero_nonunit_transcendental f hf hzero)
  apply source_valuation_coefficient_restriction_curve_residue_isAlgebraic
    (A := A) (F := F) C E (pencilCoefficientCurveParameter (E := E) t) f hf hzero
  · exact hvalue.trans (pencilCoefficientCurveParameter_value (E := E) t).symm
  · exact (pencilCoefficientCurveField_trdeg_one t ht).le

end DimensionFourDependence
