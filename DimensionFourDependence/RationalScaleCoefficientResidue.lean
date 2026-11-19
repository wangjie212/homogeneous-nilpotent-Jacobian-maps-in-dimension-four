import DimensionFourDependence.RationalScaleZeroLocalRing
import DimensionFourDependence.CoefficientRestrictionResidueRealization
import DimensionFourDependence.RegularPencilCoefficientResidue

/-! # Restricted scale coefficients specialize inside the original relative constant closure -/

namespace DimensionFourDependence

attribute [local instance 2000] Algebra.toSMul

universe u

set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 100000

variable (B F : Type u) [Field B] [Field F] [Algebra B F]

local notation "A" => rationalScaleZeroLocalRing F
local notation "G" => RatFunc F
local notation "D" => pencilCoefficientCurveField (E := B) (RatFunc.X : G)
local notation "V" => coefficientRestrictionValuationSubring («A» := A) (F := G) (D)

local instance rationalScaleCoefficientResidueDvr : IsDiscreteValuationRing A := rationalScaleZeroLocalRing_isDVR F
noncomputable local instance rationalScaleCoefficientResidueFractionAlgebra : Algebra A G := rationalScaleZeroFractionAlgebra F
local instance rationalScaleCoefficientResidueFractionRing : IsFractionRing A G := rationalScaleZeroFraction_isFractionRing F
local instance rationalScaleCoefficientResidueSourceTower : IsScalarTower B A G := by
  letI : IsScalarTower F A G := rationalScaleZeroFraction_scalarTower F
  exact IsScalarTower.to₁₃₄ B F A G
local instance rationalScaleCoefficientResidueCurveTower : IsScalarTower B (D) G :=
  pencilCoefficientCurveField_scalarTower (E := B) RatFunc.X

/-- Evaluation at zero preserves the original intermediate constants. -/
noncomputable def rationalScaleZeroEvaluationAlgHom : A →ₐ[B] F :=
  { rationalScaleZeroEvaluation F with
    commutes' b := by
      rw [IsScalarTower.algebraMap_apply B F A]
      exact rationalScaleZeroEvaluation_constant F (algebraMap B F b) }

/-- The same evaluation is local under its constant-compatible interface. -/
theorem rationalScaleZeroEvaluationAlgHom_isLocalHom :
    IsLocalHom (rationalScaleZeroEvaluationAlgHom B F).toRingHom :=
  rationalScaleZeroEvaluation_isLocalHom F

/-- The actual scale-zero restriction realizes its entire coefficient
residue field inside the original source field, preserving B. -/
noncomputable def rationalScaleRestrictedCoefficientResidueHom :
    letI := coefficientRestrictionConstantAlgebra («A» := A) (F := G) (D) B
    IsLocalRing.ResidueField (V) →ₐ[B] F := by
  letI := rationalScaleZeroEvaluationAlgHom_isLocalHom B F
  exact coefficientRestrictionResidueFieldAlgHom («A» := A) («G» := G) (D) B
    (rationalScaleZeroEvaluationAlgHom B F)

/-- The coefficient curve is the full relative closure of B(s).
The same scale zero makes its restricted residue algebraic over B. -/
theorem rationalScaleRestrictedCoefficientResidue_isAlgebraic :
    letI := coefficientRestrictionConstantAlgebra («A» := A) (F := G) (D) B
    Algebra.IsAlgebraic B (IsLocalRing.ResidueField (V)) := by
  obtain ⟨hx, hz, hv⟩ := rationalScaleZeroParameter_regular_nonzero_zero F
  exact regular_pencil_coefficient_curve_residue_isAlgebraic
    (E := B) («A» := A) (F := G) RatFunc.X
    (algebraMap (Polynomial F) A Polynomial.X) hx hz hv

/-- Every actual restricted coefficient residue belongs to the
relative algebraic closure of B in the original source field. -/
noncomputable def rationalScaleRestrictedResidueClosureHom :
    letI := coefficientRestrictionConstantAlgebra («A» := A) (F := G) (D) B
    IsLocalRing.ResidueField (V) →ₐ[B] algebraicClosure B F := by
  letI := coefficientRestrictionConstantAlgebra («A» := A) (F := G) (D) B
  letI := rationalScaleRestrictedCoefficientResidue_isAlgebraic B F
  let ψ := rationalScaleRestrictedCoefficientResidueHom B F
  exact
    { toFun := fun c => ⟨ψ c, mem_algebraicClosure_iff.mpr
        ((Algebra.IsAlgebraic.isAlgebraic (R := B) c).algHom ψ)⟩
      map_zero' := Subtype.ext (map_zero ψ)
      map_one' := Subtype.ext (map_one ψ)
      map_add' := fun c d => Subtype.ext (map_add ψ c d)
      map_mul' := fun c d => Subtype.ext (map_mul ψ c d)
      commutes' := fun c => Subtype.ext (ψ.commutes c) }

/-- The closure-valued embedding is the actual original-field
residue realization, with no replacement coefficient embedding. -/
theorem rationalScaleRestrictedResidueClosureHom_source
    (c : IsLocalRing.ResidueField (V)) :
    letI := coefficientRestrictionConstantAlgebra («A» := A) (F := G) (D) B
    algebraMap (algebraicClosure B F) F (rationalScaleRestrictedResidueClosureHom B F c) =
      rationalScaleRestrictedCoefficientResidueHom B F c := rfl

end DimensionFourDependence
