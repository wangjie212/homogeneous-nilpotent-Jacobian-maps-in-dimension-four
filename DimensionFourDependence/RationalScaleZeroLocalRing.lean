import DimensionFourDependence.LocalParameterDvr
import DimensionFourDependence.PrimeLocalizationFunctionField
import Mathlib.FieldTheory.RatFunc.AsPolynomial

/-! # The independent rational scale has its actual zero DVR and original coefficient residue -/

namespace DimensionFourDependence

attribute [local instance 2000] Algebra.toSMul

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000

variable (F : Type*) [Field F]

/-- The actual local ring at zero of the independent scale. -/
abbrev rationalScaleZeroLocalRing :=
  Localization.AtPrime (polynomialParameterZeroPrime F).asIdeal

/-- Its actual discrete valuation ring structure. -/
theorem rationalScaleZeroLocalRing_isDVR : IsDiscreteValuationRing (rationalScaleZeroLocalRing F) :=
  polynomialParameterLocalRing_isDVR F

/-- The actual local ring embeds in the same rational scale field. -/
@[instance_reducible]
noncomputable def rationalScaleZeroFractionAlgebra :
    Algebra (rationalScaleZeroLocalRing F) (RatFunc F) :=
  primeLocalizationFractionAlgebra (polynomialParameterZeroPrime F).asIdeal

/-- The rational scale field is the fraction field of this actual local ring. -/
theorem rationalScaleZeroFraction_isFractionRing :
    letI := rationalScaleZeroFractionAlgebra F
    IsFractionRing (rationalScaleZeroLocalRing F) (RatFunc F) :=
  primeLocalizationFraction_isFractionRing (polynomialParameterZeroPrime F).asIdeal

/-- The fraction-field map retains the original coefficient action. -/
theorem rationalScaleZeroFraction_scalarTower :
    letI := rationalScaleZeroFractionAlgebra F
    IsScalarTower F (rationalScaleZeroLocalRing F) (RatFunc F) :=
  primeLocalizationFraction_base_scalarTower (K := F) (F := RatFunc F) (polynomialParameterZeroPrime F).asIdeal

/-- Evaluation at zero is an actual local homomorphism on the scale DVR. -/
noncomputable def rationalScaleZeroEvaluation : rationalScaleZeroLocalRing F →+* F :=
  localParameterDvrHom (k := F) (0 : F) (by simp)

/-- This evaluation is local, so it gives the actual residue embedding. -/
theorem rationalScaleZeroEvaluation_isLocalHom : IsLocalHom (rationalScaleZeroEvaluation F) :=
  localParameterDvrHom_isLocalHom (k := F) (0 : F) (by simp)

/-- Every original coefficient has its own specified zero-scale value. -/
theorem rationalScaleZeroEvaluation_constant (c : F) :
    rationalScaleZeroEvaluation F (algebraMap F (rationalScaleZeroLocalRing F) c) = c := by
  rw [IsScalarTower.algebraMap_apply F (Polynomial F) (rationalScaleZeroLocalRing F)]
  change localParameterDvrHom (k := F) (0 : F) _
    (algebraMap (Polynomial F) (rationalScaleZeroLocalRing F) (Polynomial.C c)) = c
  rw [localParameterDvrHom_polynomial, Polynomial.aeval_C, Algebra.algebraMap_self, RingHom.id_apply]

/-- The residue of a field is identified with that same specified field. -/
noncomputable def rationalScaleFieldResidueEquiv : IsLocalRing.ResidueField F ≃+* F :=
  (RingEquiv.ofBijective (IsLocalRing.residue F)
    ⟨(IsLocalRing.residue F).injective, IsLocalRing.residue_surjective⟩).symm

/-- The actual zero-scale residue map has target the original source
coefficient field, rather than an unspecified algebraic extension. -/
noncomputable def rationalScaleZeroResidueHom :
    IsLocalRing.ResidueField (rationalScaleZeroLocalRing F) →+* F := by
  letI := rationalScaleZeroEvaluation_isLocalHom F
  exact (rationalScaleFieldResidueEquiv F).toRingHom.comp
    (IsLocalRing.ResidueField.map (rationalScaleZeroEvaluation F))

/-- Reduction followed by the original-field residue map is exactly
the actual local evaluation at zero. -/
theorem rationalScaleZeroResidueHom_residue (a : rationalScaleZeroLocalRing F) :
    rationalScaleZeroResidueHom F (IsLocalRing.residue _ a) = rationalScaleZeroEvaluation F a := by
  change (rationalScaleFieldResidueEquiv F) (IsLocalRing.residue F (rationalScaleZeroEvaluation F a)) = _
  exact RingEquiv.symm_apply_apply _ _

/-- The actual zero-scale residue map retains every original coefficient. -/
theorem rationalScaleZeroResidueHom_constant (c : F) :
    rationalScaleZeroResidueHom F (IsLocalRing.residue _
      (algebraMap F (rationalScaleZeroLocalRing F) c)) = c := by
  rw [rationalScaleZeroResidueHom_residue, rationalScaleZeroEvaluation_constant]

/-- The local zero-scale residue field is exactly the original
coefficient field, with its specified evaluation map. -/
noncomputable def rationalScaleZeroResidueEquiv :
    IsLocalRing.ResidueField (rationalScaleZeroLocalRing F) ≃+* F :=
  RingEquiv.ofBijective (rationalScaleZeroResidueHom F)
    ⟨(rationalScaleZeroResidueHom F).injective,
      fun c => ⟨IsLocalRing.residue _ (algebraMap F (rationalScaleZeroLocalRing F) c),
        rationalScaleZeroResidueHom_constant F c⟩⟩

/-- The actual local scale parameter is a nonzero regular zero in
the same rational scale field. -/
theorem rationalScaleZeroParameter_regular_nonzero_zero :
    letI := rationalScaleZeroFractionAlgebra F
    let x := algebraMap (Polynomial F) (rationalScaleZeroLocalRing F) Polynomial.X
    x ≠ 0 ∧ x ∈ IsLocalRing.maximalIdeal (rationalScaleZeroLocalRing F) ∧
      algebraMap (rationalScaleZeroLocalRing F) (RatFunc F) x = RatFunc.X := by
  letI := rationalScaleZeroFractionAlgebra F
  have hx : Irreducible (algebraMap (Polynomial F) (rationalScaleZeroLocalRing F) Polynomial.X) :=
    polynomialParameterLocal_X_irreducible F
  refine ⟨hx.ne_zero, ?_, ?_⟩
  · exact (IsLocalRing.mem_maximalIdeal _).mpr hx.not_isUnit
  · exact (primeLocalizationFractionHom_algebraMap
      (F := RatFunc F) (polynomialParameterZeroPrime F).asIdeal Polynomial.X).trans RatFunc.algebraMap_X

end DimensionFourDependence
