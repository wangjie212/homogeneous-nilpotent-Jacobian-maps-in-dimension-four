import DimensionFourDependence.NativeDivisorResidueTranscendence
import DimensionFourDependence.CoefficientResidueCurveDegreeExistence
import DimensionFourDependence.CharacteristicPencilCoefficientResidue

/-! # The actual characteristic divisor specialization has its own positive curve degree -/

namespace DimensionFourDependence

open MvPolynomial AlgebraicGeometry
open scoped TensorProduct

attribute [local instance] MvPolynomial.gradedAlgebra Algebra.TensorProduct.rightAlgebra

universe u

set_option quotPrecheck false
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {K : Type u} [Field K] [CharZero K]
  (H : Fin 4 → MvPolynomial (Fin 4) K) (I : ImageRelationWitness H)
  (E : Type u) [Field E] [Algebra (closedGaussParameterField H I) E]
  [Algebra.IsAlgebraic (closedGaussParameterField H I) E]
  {d : ℕ} (hH : IsHomogMap H d)
  (e : RatFunc K ≃ₐ[K] closedGaussParameterField H I)
  (hd : 0 < d) (hind : ¬ComponentsDependent H) (hGauss : gaussImageDimension H I = 1)

local notation "C₀" => closedGaussParameterField H I
local notation "T₀" a:max => projectiveCoordinateChartAlgebra (C := C₀)
  (rationalCoordinate (K := K) (n := 4)) ((finSuccEquiv' a).symm none) ⊗[C₀] E
local notation "N" => extendedClosedGaussNormalizationScheme H I E hH e
local notation "w" => extendedClosedGaussNormalizationHyperplaneWeight H I E hH e
local notation "z₀" a:max q:max => extendedClosedGaussNormalizationTensorChartPoint H I E hH e (finSuccEquiv' a) q
local notation "ha₀" a:max q:max => extendedClosedGaussNormalizationTensorChartPoint_mem_chart H I E hH e (finSuccEquiv' a) q
local notation "P₀" r:max => pencilCoefficientCurveField (E := E)
  (nativeCharacteristicPencilValue H I E hH e hd hind hGauss r)

local instance nativePencilDivisorCurveDegreeExistenceIntegral : IsIntegral N :=
  extendedClosedGaussNormalizationScheme_isIntegral H I E hH e
noncomputable local instance nativePencilDivisorCurveDegreeExistenceAlgebra : Algebra E (N).functionField :=
  extendedClosedGaussOwnFunctionFieldAlgebra H I E hH e

/-- At each actual normalization divisor with algebraic pencil
coefficient residue, the actual source-coordinate image has its own
positive Hilbert degree, bounded by the actual generic pencil degree.
Neither positivity nor a specialized curve degree is assumed. -/
theorem actual_characteristic_pencil_divisor_curve_degree_exists
    (r : (N).functionField)
    (a : Fin 4) (q : PrimeSpectrum (normalizationRing (T₀ a))) (hq : q.asIdeal.height = 1)
    (hz : Order.coheight (z₀ a q) = 1)
    (hres : NativeCharacteristicPencilCoefficientResidueAlgebraic H I E hH e hd hind hGauss r (z₀ a q) hz)
    {D : ℕ} (hD : HasCurveHilbertDegree (projectiveFieldPointIdeal (E := P₀ r) (w)).toIdeal D) :
    letI := extendedClosedGaussNormalization_divisor_stalk_isDVR H I E hH e (z₀ a q) hz
    letI := coefficientRestrictionResidueAlgebra
      (A := (N).presheaf.stalk (z₀ a q)) (F := (N).functionField) (P₀ r)
    ∃ D' : ℕ, D' ≤ D ∧ HasCurveHilbertDegree
      (projectiveFieldPointIdeal
        (E := IsLocalRing.ResidueField (coefficientRestrictionValuationSubring
          (A := (N).presheaf.stalk (z₀ a q)) (F := (N).functionField) (P₀ r)))
        (fun i => IsLocalRing.residue ((N).presheaf.stalk (z₀ a q))
          (nativeProjectiveCoordinateGerm H I E hH e (z₀ a q) a (ha₀ a q) i))).toIdeal D' := by
  letI := extendedClosedGaussNormalization_divisor_stalk_isDVR H I E hH e (z₀ a q) hz
  letI := extendedClosedGaussStalkCoefficientAlgebra H I E hH e (z₀ a q)
  letI := extendedClosedGaussStalkCoefficientAlgebra_scalarTower H I E hH e (z₀ a q)
  letI := pencilCoefficientCurveField_scalarTower (E := E)
    (nativeCharacteristicPencilValue H I E hH e hd hind hGauss r)
  letI := coefficientRestrictionResidueAlgebra
    (A := (N).presheaf.stalk (z₀ a q)) (F := (N).functionField) (P₀ r)
  obtain ⟨i, hi⟩ := actual_native_divisor_has_transcendental_original_coordinate_residue
    H I E hH e hGauss a q hq
  apply source_valuation_coefficient_residue_curve_degree_exists
    (E := E) (A := (N).presheaf.stalk (z₀ a q)) (F := (N).functionField) (P₀ r) hres
    (w) ((w) a)⁻¹ (inv_ne_zero (extendedClosedGaussNormalizationHyperplaneWeight_ne_zero H I E hH e a))
    (nativeProjectiveCoordinateGerm H I E hH e (z₀ a q) a (ha₀ a q))
    (fun j => by rw [nativeProjectiveCoordinateGerm_value, div_eq_mul_inv, mul_comm])
    a i (nativeProjectiveCoordinateGerm_frame H I E hH e (z₀ a q) a (ha₀ a q)) hi hD

end DimensionFourDependence
