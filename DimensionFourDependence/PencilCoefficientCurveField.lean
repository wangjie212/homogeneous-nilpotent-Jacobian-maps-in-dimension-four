import DimensionFourDependence.ProjectiveOutputField
import Mathlib.FieldTheory.AlgebraicClosure

/-! # The actual relatively closed coefficient curve of a rational pencil -/

namespace DimensionFourDependence

universe u

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000

variable {E F : Type u} [Field E] [Field F] [Algebra E F]

/-- The actual relative algebraic closure of E(t) inside the original
source function field, retaining the specified pencil parameter. -/
@[reducible]
noncomputable def pencilCoefficientCurveField (t : F) :
    IntermediateField (IntermediateField.adjoin E {t}) F :=
  algebraicClosure (IntermediateField.adjoin E {t}) F

/-- The original constant-field action agrees through the pencil's
relative coefficient closure and the native source field. -/
theorem pencilCoefficientCurveField_scalarTower (t : F) :
    IsScalarTower E (pencilCoefficientCurveField (E := E) t) F :=
  IsScalarTower.to₁₃₄ E (IntermediateField.adjoin E {t})
    (pencilCoefficientCurveField (E := E) t) F

/-- The actual pencil parameter, viewed in its relatively closed
coefficient curve field. -/
noncomputable def pencilCoefficientCurveParameter (t : F) : pencilCoefficientCurveField (E := E) t :=
  algebraMap (IntermediateField.adjoin E {t}) (pencilCoefficientCurveField (E := E) t)
    ⟨t, IntermediateField.subset_adjoin E {t} rfl⟩

/-- Its field realization is the original pencil value, without a
change of parameter or an unspecified field equivalence. -/
theorem pencilCoefficientCurveParameter_value (t : F) :
    algebraMap (pencilCoefficientCurveField (E := E) t) F
      (pencilCoefficientCurveParameter (E := E) t) = t := rfl

/-- A transcendental pencil gives an actual one-dimensional
coefficient field even after taking its full relative algebraic closure. -/
theorem pencilCoefficientCurveField_trdeg_one (t : F) (ht : Transcendental E t) :
    Algebra.trdeg E (pencilCoefficientCurveField (E := E) t) = 1 := by
  let : FaithfulSMul (IntermediateField.adjoin E {t}) (pencilCoefficientCurveField (E := E) t) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr
      (algebraMap (IntermediateField.adjoin E {t}) (pencilCoefficientCurveField (E := E) t)).injective
  have htr := trdeg_add_eq (A := pencilCoefficientCurveField (E := E) t)
    E (IntermediateField.adjoin E {t})
  have hz : Algebra.trdeg (IntermediateField.adjoin E {t})
      (pencilCoefficientCurveField (E := E) t) = 0 := trdeg_eq_zero
  rw [hz, add_zero, generatedField_singleton_trdeg_one_of_transcendental t ht] at htr
  exact htr.symm

/-- The chosen coefficient curve has no further algebraic constants
inside the same native source field. -/
theorem pencilCoefficientCurveField_relatively_closed (t : F) :
    algebraicClosure (pencilCoefficientCurveField (E := E) t) F = ⊥ :=
  algebraicClosure.algebraicClosure_eq_bot (IntermediateField.adjoin E {t}) F

end DimensionFourDependence
