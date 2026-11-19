import DimensionFourDependence.ExtendedPencilAmbientPullbacks
import DimensionFourDependence.ExtendedNormalizedChartPullbacks
import DimensionFourDependence.ExtendedNormalizationHyperplaneSheaf

/-! # Original ambient tensor values equal the normalized pencil's rational frame ratios -/

namespace DimensionFourDependence

open MvPolynomial AlgebraicGeometry CategoryTheory
open scoped TensorProduct

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

variable {K : Type u} [Field K] [CharZero K]
  (H : Fin 4 → MvPolynomial (Fin 4) K) (I : ImageRelationWitness H)
  (E : Type u) [Field E] [Algebra (closedGaussParameterField H I) E]
  [Algebra.IsAlgebraic (closedGaussParameterField H I) E]
  {d : ℕ} (hH : IsHomogMap H d)
  (e : RatFunc K ≃ₐ[K] closedGaussParameterField H I)
  (s : Fin 4 ≃ Option (Fin 3))

local notation "C₀" => closedGaussParameterField H I
local notation "zₑ" => primeQuotientCoordinate (extendedClosedGaussPencilIdeal H I E)
local notation "T₀" => projectiveCoordinateChartAlgebra (C := C₀)
  (rationalCoordinate (K := K) (n := 4)) (s.symm none) ⊗[C₀] E
local notation "N" => extendedClosedGaussNormalizationScheme H I E hH e
local notation "Uₚ" => extendedClosedGaussPencilChartOpen H I E hH e s
local notation "Uₙ" => extendedClosedGaussNormalizationChartOpen H I E hH e s
local notation "Uₑ" => Proj.basicOpen (homogeneousSubmodule (Fin 4) E) (X (s.symm none))
local notation "f" => extendedClosedGaussNormalizationProjectiveMap H I E hH e

local instance extendedNormalizedAmbientValuesIntegral : IsIntegral N := extendedClosedGaussNormalizationScheme_isIntegral H I E hH e
local instance extendedNormalizedAmbientValuesDomain : IsDomain T₀ := original_tensor_pencil_chart_isDomain H I E s
local instance extendedNormalizedAmbientValuesNonempty : Nonempty Uₙ := extendedClosedGaussNormalizationChartOpen_nonempty H I E hH e s

/-- The actual ambient projective pullback through the pencil and
normalization, with its original normalized target chart fixed. -/
noncomputable def extendedClosedGaussNormalizedAmbientChartPullback :
    Γ(AlgebraicGeometry.Proj (homogeneousSubmodule (Fin 4) E), Uₑ) →+* Γ(N, Uₙ) :=
  (extendedClosedGaussNormalizationChartPullback H I E hH e s).comp
    (extendedClosedGaussPencilAmbientChartPullback H I E hH e s)

/-- The two actual chart pullbacks compose to the original actual
projective morphism's pullback. -/
theorem extendedClosedGaussNormalizedAmbientChartPullback_eq_app
    (r : Γ(AlgebraicGeometry.Proj (homogeneousSubmodule (Fin 4) E), Uₑ)) :
    extendedClosedGaussNormalizedAmbientChartPullback H I E hH e s r = (f).app Uₑ r := by
  have h := Scheme.Hom.appLE_comp_appLE
    (extendedClosedGaussNormalizationSchemeMap H I E hH e)
    (extendedClosedGaussPencilSchemeInclusion H I E hH e)
    Uₑ Uₚ ((f) ⁻¹ᵁ Uₑ) le_rfl le_rfl
  have h' := ConcreteCategory.congr_hom h r
  change extendedClosedGaussNormalizedAmbientChartPullback H I E hH e s r =
    (f).appLE Uₑ ((f) ⁻¹ᵁ Uₑ) le_rfl r at h'
  exact h'.trans (ConcreteCategory.congr_hom (Scheme.Hom.appLE_eq_app f) r)

/-- The entire original ambient-section tensor value maps to the
actual generic germ of its normalized geometric pullback. -/
theorem extendedClosedGaussTensorChartToOwnFunctionField_ambient_section
    (r : Γ(AlgebraicGeometry.Proj (homogeneousSubmodule (Fin 4) E), Uₑ)) :
    extendedClosedGaussTensorChartToOwnFunctionField H I E hH e s
        (extendedClosedGaussPencilAmbientSectionHom H I E hH e s r) =
      (N).germToFunctionField Uₙ
        (extendedClosedGaussNormalizedAmbientChartPullback H I E hH e s r) := by
  exact (congrArg (extendedClosedGaussTensorChartToOwnFunctionField H I E hH e s)
    (extendedClosedGaussPencilTensorChartSectionEquiv_ambient_pullback H I E hH e s r).symm).trans
      (extendedClosedGaussTensorChartToOwnFunctionField_pencil_section H I E hH e s
        (extendedClosedGaussPencilAmbientChartPullback H I E hH e s r))

/-- The original tensor coordinate ratio has exactly its native
projective rational value in the actual normalized pencil function field. -/
theorem extendedClosedGaussTensorChartToOwnFunctionField_coordinate (i : Fin 4) :
    extendedClosedGaussTensorChartToOwnFunctionField H I E hH e s
        ((extendedClosedGaussRatioCoordinateEquiv H I E hH e s).symm
          (projectiveChartTransition (C := E) zₑ (s.symm none) i)) =
      projectivePullbackRationalCoordinate N f
        (extendedClosedGaussNormalizationProjectiveMap_chart_nonempty H I E hH e)
        (s.symm none) i := by
  let r := projectiveCoordinateRatioSection E (s.symm none) i
  have hval := extendedClosedGaussTensorChartToOwnFunctionField_ambient_section H I E hH e s r
  have hcoord := extendedClosedGaussPencilAmbientSectionHom_coordinate H I E hH e s i
  exact (congrArg (extendedClosedGaussTensorChartToOwnFunctionField H I E hH e s) hcoord.symm).trans
    (hval.trans (congrArg (fun q : Γ(N, Uₙ) => (N).germToFunctionField Uₙ q)
      (extendedClosedGaussNormalizedAmbientChartPullback_eq_app H I E hH e s r)))

/-- Original tensor coordinate ratios are precisely quotients of
the actual original hyperplane frame weights. -/
theorem extendedClosedGaussTensorChartToOwnFunctionField_coordinate_weight (i : Fin 4) :
    extendedClosedGaussTensorChartToOwnFunctionField H I E hH e s
        ((extendedClosedGaussRatioCoordinateEquiv H I E hH e s).symm
          (projectiveChartTransition (C := E) zₑ (s.symm none) i)) =
      extendedClosedGaussNormalizationHyperplaneWeight H I E hH e i /
        extendedClosedGaussNormalizationHyperplaneWeight H I E hH e (s.symm none) := by
  exact (extendedClosedGaussTensorChartToOwnFunctionField_coordinate H I E hH e s i).trans
    (projectivePullbackRationalCoordinate_div N f
      (extendedClosedGaussNormalizationProjectiveMap_chart_nonempty H I E hH e)
      (s.symm none) 0 i)

end DimensionFourDependence
