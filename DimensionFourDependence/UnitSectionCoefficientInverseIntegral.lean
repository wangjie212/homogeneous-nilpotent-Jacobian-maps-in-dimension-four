import DimensionFourDependence.ProjectiveConeRootLift
import DimensionFourDependence.ExtendedProductPowerMultiplicity
import DimensionFourDependence.ExtendedOwnCoordinateCharts

/-! # Unit section coefficients give integral inverses in the actual projective coordinate charts -/

namespace DimensionFourDependence

/-- The homogenized section times the original inverse chart
coefficient gives the same original homogeneous coordinate. -/
theorem projectiveConeRadialLift_mul_constant_div
    {E F : Type*} [Field E] [Field F] [Algebra E F]
    (x : Fin 3 → F) (hgen : IntermediateField.adjoin E (Set.range x) = ⊤)
    (u v : F) (hu : u ≠ 0) :
    projectiveConeRadialLift x hgen u * projectiveConeFractionConstantHom x hgen (v / u) =
      projectiveConeRadialLift x hgen v := by
  dsimp only [projectiveConeRadialLift]
  have he : u * (v / u) = v := by field_simp
  have hc := (map_mul (projectiveConeFractionConstantHom x hgen) u (v / u)).symm.trans
    (congrArg (projectiveConeFractionConstantHom x hgen) he)
  calc
    _ = (projectiveConeFractionConstantHom x hgen u * projectiveConeFractionConstantHom x hgen (v / u)) *
        algebraMap (projectiveConeCoordinateAlgebra (E := E) x)
          (FractionRing (projectiveConeCoordinateAlgebra (E := E) x)) (projectiveConeCoordinate (E := E) x none) := by ring
    _ = _ := congrArg (fun z => z * algebraMap (projectiveConeCoordinateAlgebra (E := E) x)
      (FractionRing (projectiveConeCoordinateAlgebra (E := E) x)) (projectiveConeCoordinate (E := E) x none)) hc

open AlgebraicGeometry
open scoped TensorProduct

attribute [local instance] Algebra.TensorProduct.rightAlgebra

universe u

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option quotPrecheck false

variable {K : Type u} [Field K] [CharZero K]
  (H : Fin 4 → MvPolynomial (Fin 4) K) (I : ImageRelationWitness H)
  (E : Type u) [Field E] [Algebra (closedGaussParameterField H I) E]
  [Algebra.IsAlgebraic (closedGaussParameterField H I) E]
  {d : ℕ} (hH : IsHomogMap H d)
  (e : RatFunc K ≃ₐ[K] closedGaussParameterField H I)

local notation "N" => extendedClosedGaussNormalizationScheme H I E hH e
local notation "M" => extendedClosedGaussNormalizationHyperplaneModuleSheaf H I E hH e
local notation "w" => extendedClosedGaussNormalizationHyperplaneWeight H I E hH e
local notation "V" a:max => extendedClosedGaussNormalizationChartOpen H I E hH e (finSuccEquiv' a)

local instance unitSectionCoefficientInverseIntegralIntegral : IsIntegral N :=
  extendedClosedGaussNormalizationScheme_isIntegral H I E hH e
local instance unitSectionCoefficientInverseIntegralNonempty (a : Fin 4) : Nonempty (V a) :=
  extendedClosedGaussNormalizationChartOpen_nonempty H I E hH e (finSuccEquiv' a)
noncomputable local instance unitSectionCoefficientInverseIntegralAlgebra : Algebra E (N).functionField :=
  extendedClosedGaussOwnFunctionFieldAlgebra H I E hH e

/-- An invertible actual regular section coefficient supplies an
inverse integral over the entire actual original affine coordinate
algebra. The rational value and its nonzero denominator are both derived. -/
theorem extendedClosedGauss_unit_section_coefficient_inverse_isIntegral
    (s : Γ(M, ⊤)) (a : Fin 4)
    (hunit : IsUnit (extendedClosedGaussHyperplaneGlobalCoefficient H I E hH e s a)) :
    IsIntegral (projectiveCoordinateChartAlgebra (C := E) w a)
      (w a / extendedClosedGaussHyperplaneGlobalValue H I E hH e s) := by
  let c := extendedClosedGaussHyperplaneGlobalCoefficient H I E hH e s a
  let φ : Γ(N, V a) →+* (N).functionField := ((N).germToFunctionField (V a)).hom
  obtain ⟨v, hcv⟩ := hunit.exists_right_inv
  have hc : φ c = extendedClosedGaussHyperplaneGlobalValue H I E hH e s / w a :=
    rationalFrameGlobalCoefficient_generic_value N (fun a : Fin 4 => V a) w
      (extendedClosedGaussNormalizationChartOpen_iSup H I E hH e)
      (extendedClosedGaussNormalizationHyperplaneWeight_ne_zero H I E hH e) s a
  have hprod : (extendedClosedGaussHyperplaneGlobalValue H I E hH e s / w a) * φ v = 1 :=
    (congrArg (fun z : (N).functionField => z * φ v) hc.symm).trans
      ((map_mul φ c v).symm.trans ((congrArg φ hcv).trans (map_one φ)))
  have hu : extendedClosedGaussHyperplaneGlobalValue H I E hH e s ≠ 0 := by
    intro hzero
    rw [hzero, zero_div, zero_mul] at hprod
    exact zero_ne_one hprod
  have hmul : extendedClosedGaussHyperplaneGlobalValue H I E hH e s * φ v = w a :=
    (div_eq_one_iff_eq (extendedClosedGaussNormalizationHyperplaneWeight_ne_zero H I E hH e a)).mp
      (by simpa only [div_mul_eq_mul_div] using hprod)
  have hv : φ v = w a / extendedClosedGaussHyperplaneGlobalValue H I E hH e s :=
    (eq_div_iff hu).mpr ((mul_comm _ _).trans hmul)
  have hi := extendedClosedGaussNormalizedChartFunction_isIntegral_own_coordinates H I E hH e (finSuccEquiv' a) v
  exact hv ▸ hi

end DimensionFourDependence
