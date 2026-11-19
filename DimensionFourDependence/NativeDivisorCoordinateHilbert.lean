import DimensionFourDependence.NativePolynomialGermHom
import DimensionFourDependence.CoefficientRestrictionHilbertComparison

/-! # Actual projective coordinates and the intrinsic divisor degree comparison -/

namespace DimensionFourDependence

open MvPolynomial AlgebraicGeometry

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

variable {K : Type u} [Field K] [CharZero K]
  (H : Fin 4 → MvPolynomial (Fin 4) K) (I : ImageRelationWitness H)
  (E : Type u) [Field E] [Algebra (closedGaussParameterField H I) E]
  [Algebra.IsAlgebraic (closedGaussParameterField H I) E]
  {d : ℕ} (hH : IsHomogMap H d)
  (e : RatFunc K ≃ₐ[K] closedGaussParameterField H I)

local notation "N" => extendedClosedGaussNormalizationScheme H I E hH e
local notation "U" a:max => extendedClosedGaussNormalizationChartOpen H I E hH e (finSuccEquiv' a)
local notation "w" => extendedClosedGaussNormalizationHyperplaneWeight H I E hH e

local instance nativeDivisorCoordinateHilbertIntegral : IsIntegral N :=
  extendedClosedGaussNormalizationScheme_isIntegral H I E hH e
noncomputable local instance nativeDivisorCoordinateHilbertAlgebra : Algebra E (N).functionField :=
  extendedClosedGaussOwnFunctionFieldAlgebra H I E hH e

/-- The actual regular source coordinates in an original projective chart. -/
noncomputable def nativeProjectiveCoordinateGerm
    (z : N) (a : Fin 4) (ha : z ∈ U a) (i : Fin 4) : (N).presheaf.stalk z :=
  nativePolynomialCoefficientGermHom H I E hH e z a ha (X i)

/-- Their native function-field values are exactly the original coordinate ratios. -/
theorem nativeProjectiveCoordinateGerm_value
    (z : N) (a : Fin 4) (ha : z ∈ U a) (i : Fin 4) :
    algebraMap ((N).presheaf.stalk z) (N).functionField
      (nativeProjectiveCoordinateGerm H I E hH e z a ha i) = w i / w a := by
  unfold nativeProjectiveCoordinateGerm
  rw [nativePolynomialCoefficientGermHom_apply,
    extendedClosedGaussPolynomialCoefficientGerm_value H I E hH e _ (isHomogeneous_X _ _),
    aeval_X, pow_one]

/-- The chart coordinate is one in the actual local ring, so its
specialization remains a nonzero projective coordinate. -/
theorem nativeProjectiveCoordinateGerm_frame
    (z : N) (a : Fin 4) (ha : z ∈ U a) :
    nativeProjectiveCoordinateGerm H I E hH e z a ha a = 1 := by
  apply IsFractionRing.injective ((N).presheaf.stalk z) (N).functionField
  rw [nativeProjectiveCoordinateGerm_value, div_self
    (extendedClosedGaussNormalizationHyperplaneWeight_ne_zero H I E hH e a), map_one]

/-- Every intrinsic source divisor constructs its valuation and
coefficient residue field, and bounds the Hilbert function of its actual
source-coordinate residues by that of the original generic coordinates. -/
theorem native_normalization_divisor_projective_hilbert_bound
    (z : N) (hz : Order.coheight z = 1) (a : Fin 4) (ha : z ∈ U a)
    (C : Type*) [Field C] [Algebra C (N).functionField] (n : ℕ) :
    letI := extendedClosedGaussNormalization_divisor_stalk_isDVR H I E hH e z hz
    letI := coefficientRestrictionResidueAlgebra
      (A := (N).presheaf.stalk z) (F := (N).functionField) C
    projectiveHilbertFunction
      (projectiveFieldPointIdeal
        (E := IsLocalRing.ResidueField (coefficientRestrictionValuationSubring
          (A := (N).presheaf.stalk z) (F := (N).functionField) C))
        (fun i => IsLocalRing.residue ((N).presheaf.stalk z)
          (nativeProjectiveCoordinateGerm H I E hH e z a ha i))).toIdeal n ≤
      projectiveHilbertFunction (projectiveFieldPointIdeal (E := C) w).toIdeal n := by
  letI := extendedClosedGaussNormalization_divisor_stalk_isDVR H I E hH e z hz
  letI := coefficientRestrictionResidueAlgebra
    (A := (N).presheaf.stalk z) (F := (N).functionField) C
  have hb := source_valuation_coefficient_restriction_hilbert_bound
    (A := (N).presheaf.stalk z) (F := (N).functionField) C
    (nativeProjectiveCoordinateGerm H I E hH e z a ha) n
  have hv : (fun i => algebraMap ((N).presheaf.stalk z) (N).functionField
      (nativeProjectiveCoordinateGerm H I E hH e z a ha i)) =
      (fun i => (w a)⁻¹ * w i) := by
    funext i
    rw [nativeProjectiveCoordinateGerm_value, div_eq_mul_inv, mul_comm]
  rw [hv, projectiveFieldPointIdeal_scale w (w a)⁻¹
    (inv_ne_zero (extendedClosedGaussNormalizationHyperplaneWeight_ne_zero H I E hH e a))] at hb
  exact hb

/-- The same actual intrinsic divisor cannot increase the projective
curve degree over the coefficient residue field it constructs. -/
theorem native_normalization_divisor_projective_curve_degree_bound
    (z : N) (hz : Order.coheight z = 1) (a : Fin 4) (ha : z ∈ U a)
    (C : Type*) [Field C] [Algebra C (N).functionField] {D D' : ℕ}
    (hD : HasCurveHilbertDegree (projectiveFieldPointIdeal (E := C) w).toIdeal D) :
    letI := extendedClosedGaussNormalization_divisor_stalk_isDVR H I E hH e z hz
    letI := coefficientRestrictionResidueAlgebra
      (A := (N).presheaf.stalk z) (F := (N).functionField) C
    HasCurveHilbertDegree
      (projectiveFieldPointIdeal
        (E := IsLocalRing.ResidueField (coefficientRestrictionValuationSubring
          (A := (N).presheaf.stalk z) (F := (N).functionField) C))
        (fun i => IsLocalRing.residue ((N).presheaf.stalk z)
          (nativeProjectiveCoordinateGerm H I E hH e z a ha i))).toIdeal D' → D' ≤ D := by
  letI := extendedClosedGaussNormalization_divisor_stalk_isDVR H I E hH e z hz
  letI := coefficientRestrictionResidueAlgebra
    (A := (N).presheaf.stalk z) (F := (N).functionField) C
  intro hD'
  exact curveHilbertDegree_le_of_hilbertFunction_le _ _
    (fun n => native_normalization_divisor_projective_hilbert_bound H I E hH e z hz a ha C n)
    hD hD'

end DimensionFourDependence
