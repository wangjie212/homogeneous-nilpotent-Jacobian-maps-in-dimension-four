import DimensionFourDependence.ExtendedNativeNormalizedSections
import DimensionFourDependence.ExtendedOwnFunctionFieldEquiv
import DimensionFourDependence.ProjectiveNormalizedSectionFieldMap
import DimensionFourDependence.ProjectiveAffineRatioCoordinates

/-! # Actual global pencil sections in the original tensor fraction fields -/

namespace DimensionFourDependence

open AlgebraicGeometry
open scoped TensorProduct

attribute [local instance] Algebra.TensorProduct.rightAlgebra

universe u

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 2000000
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

variable {K : Type u} [Field K] [CharZero K]
  (H : Fin 4 → MvPolynomial (Fin 4) K) (I : ImageRelationWitness H)
  (E : Type u) [Field E] [Algebra (closedGaussParameterField H I) E]
  [Algebra.IsAlgebraic (closedGaussParameterField H I) E]
  {d : ℕ} (hH : IsHomogMap H d)
  (e : RatFunc K ≃ₐ[K] closedGaussParameterField H I)

local notation "C₀" => closedGaussParameterField H I
local notation "T" t:max => projectiveCoordinateChartAlgebra (C := C₀)
  (rationalCoordinate (K := K) (n := 4)) (Equiv.symm t none) ⊗[C₀] E
local notation "N" => extendedClosedGaussNormalizationScheme H I E hH e
local notation "M" => extendedClosedGaussNormalizationHyperplaneModuleSheaf H I E hH e
local notation "w" => extendedClosedGaussNormalizationHyperplaneWeight H I E hH e

local instance extendedOriginalSectionRepresentationIntegral : IsIntegral N := extendedClosedGaussNormalizationScheme_isIntegral H I E hH e
local instance extendedOriginalSectionRepresentationDomain (t : Fin 4 ≃ Option (Fin 3)) : IsDomain (T t) :=
  original_tensor_pencil_chart_isDomain H I E t
noncomputable local instance extendedOriginalSectionRepresentationAlgebra : Algebra E (N).functionField :=
  extendedClosedGaussOwnFunctionFieldAlgebra H I E hH e

variable (t : Fin 4 ≃ Option (Fin 3))

/-- The actual original projective frame coordinates in a specified
original tensor chart's own fraction field. -/
noncomputable def extendedClosedGaussOriginalFrameCoordinates : Fin 4 → FractionRing (T t) :=
  (extendedClosedGaussNormalizedChartFunctionFieldAlgEquiv H I E hH e t).symm ∘ w

/-- Each constructed original frame coordinate is nonzero. -/
theorem extendedClosedGaussOriginalFrameCoordinates_ne_zero (i : Fin 4) :
    extendedClosedGaussOriginalFrameCoordinates H I E hH e t i ≠ 0 := by
  intro hzero
  apply extendedClosedGaussNormalizationHyperplaneWeight_ne_zero H I E hH e i
  apply (extendedClosedGaussNormalizedChartFunctionFieldAlgEquiv H I E hH e t).symm.injective
  exact hzero.trans (map_zero _).symm

/-- The constructed original field coordinates have exactly the
three original tensor coordinate ratios required by the section degree bound. -/
theorem extendedClosedGaussOriginalFrameCoordinates_ratios :
    projectiveAffineRatioCoordinates (extendedClosedGaussOriginalFrameCoordinates H I E hH e t) t =
      (fun i => algebraMap (T t) (FractionRing (T t)) (originalTensorPencilCoordinate H I E t i)) := by
  let b := extendedClosedGaussNormalizedChartFunctionFieldAlgEquiv H I E hH e t
  exact (projectiveAffineRatioCoordinates_field_map w b.symm.toRingHom t).trans
    (funext (extendedClosedGaussNormalizedChartFunctionFieldAlgEquiv_symm_coordinate H I E hH e t))

/-- Every actual global native pencil section constructs an original
normalized-frame section in any specified original tensor fraction field. -/
noncomputable def extendedClosedGaussHyperplaneOriginalNormalizedSection (s : Γ(M, ⊤)) :
    ProjectiveNormalizedSection (k := E) (extendedClosedGaussOriginalFrameCoordinates H I E hH e t) :=
  projectiveNormalizedSectionFieldMap w
    (extendedClosedGaussNormalizedChartFunctionFieldAlgEquiv H I E hH e t).symm
    (extendedClosedGaussHyperplaneProjectiveNormalizedSection H I E hH e s)

/-- The original normalized-frame representation retains every
native global section coefficient under the actual field identification. -/
theorem extendedClosedGaussHyperplaneOriginalNormalizedSection_coefficient
    (s : Γ(M, ⊤)) (a : Fin 4) :
    ((extendedClosedGaussHyperplaneOriginalNormalizedSection H I E hH e t s).coefficient a :
        FractionRing (T t)) =
      (extendedClosedGaussNormalizedChartFunctionFieldAlgEquiv H I E hH e t).symm
        (extendedClosedGaussHyperplaneOwnCoefficient H I E hH e s a) := rfl

/-- A nonzero actual global native section supplies a nonzero
coefficient in every original tensor fraction-field representation. -/
theorem extendedClosedGaussHyperplaneOriginalNormalizedSection_coefficient_ne_zero
    (s : Γ(M, ⊤)) (hs : s ≠ 0) (a : Fin 4) :
    ((extendedClosedGaussHyperplaneOriginalNormalizedSection H I E hH e t s).coefficient a :
        FractionRing (T t)) ≠ 0 := by
  intro hzero
  apply extendedClosedGaussHyperplaneOwnCoefficient_ne_zero H I E hH e s hs a
  apply (extendedClosedGaussNormalizedChartFunctionFieldAlgEquiv H I E hH e t).symm.injective
  exact hzero.trans (map_zero _).symm

/-- On each of the original four affine charts, the original-frame
representation's coefficient is exactly the actual chart coefficient's
original canonical fraction value. -/
theorem extendedClosedGaussHyperplaneOriginalNormalizedSection_original_coefficient
    (s : Γ(M, ⊤)) (a : Fin 4) :
    ((extendedClosedGaussHyperplaneOriginalNormalizedSection H I E hH e (finSuccEquiv' a) s).coefficient a :
        FractionRing (T (finSuccEquiv' a))) =
      extendedClosedGaussHyperplaneOriginalCoefficient H I E hH e s a := by
  let b := extendedClosedGaussNormalizedChartFunctionFieldAlgEquiv H I E hH e (finSuccEquiv' a)
  change b.symm (extendedClosedGaussHyperplaneOwnCoefficient H I E hH e s a) = _
  apply b.injective
  rw [AlgEquiv.apply_symm_apply]
  exact (extendedClosedGaussNormalizedChartFunctionFieldEquiv_section H I E hH e (finSuccEquiv' a)
    (extendedClosedGaussHyperplaneGlobalCoefficient H I E hH e s a)).symm

end DimensionFourDependence
