import DimensionFourDependence.AffineChartSectionNaturality
import DimensionFourDependence.ExtendedNormalizationFunctionField
import DimensionFourDependence.ExtendedGaussNormalizationMorphism

/-! # Original tensor values agree with actual normalized section pullbacks -/

namespace DimensionFourDependence

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct

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
local notation "T₀" => projectiveCoordinateChartAlgebra (C := C₀)
  (rationalCoordinate (K := K) (n := 4)) (s.symm none) ⊗[C₀] E
local notation "N₀" => normalizationRing T₀
local notation "P" => extendedClosedGaussPencilScheme H I E hH e
local notation "N" => extendedClosedGaussNormalizationScheme H I E hH e
local notation "Uₚ" => extendedClosedGaussPencilChartOpen H I E hH e s
local notation "Uₙ" => extendedClosedGaussNormalizationChartOpen H I E hH e s
local notation "n" => extendedClosedGaussNormalizationSchemeMap H I E hH e

local instance : IsIntegral N := extendedClosedGaussNormalizationScheme_isIntegral H I E hH e
local instance : IsDomain T₀ := original_tensor_pencil_chart_isDomain H I E s
local instance : Nonempty Uₙ := extendedClosedGaussNormalizationChartOpen_nonempty H I E hH e s

/-- The actual normalization section pullback with its original
normalized chart as the explicitly specified target open. -/
noncomputable def extendedClosedGaussNormalizationChartPullback : Γ(P, Uₚ) →+* Γ(N, Uₙ) :=
  ((n).appLE Uₚ Uₙ le_rfl).hom

/-- Normalization pulls every actual pencil chart section back to
its canonical original tensor value in the actual normalization ring. -/
theorem extendedClosedGaussNormalizedChartSectionEquiv_pencil_pullback (r : Γ(P, Uₚ)) :
    extendedClosedGaussNormalizedChartSectionEquiv H I E hH e s (extendedClosedGaussNormalizationChartPullback H I E hH e s r) =
      algebraMap T₀ N₀ (extendedClosedGaussPencilTensorChartSectionEquiv H I E hH e s r) := by
  exact affineChartSectionEquiv_pullback Uₙ (CommRingCat.of N₀)
    (extendedClosedGaussNormalizationTensorChartIso H I E hH e s) n
    ⟨Uₚ, extendedClosedGaussPencilChartOpen_isAffineOpen H I E hH e s⟩
    (CommRingCat.ofHom ((algebraMap T₀ N₀).comp
      (extendedClosedGaussPencilTensorChartSectionEquiv H I E hH e s).toRingHom))
    (extendedClosedGaussNormalizationTensorChartInclusion_to_base H I E hH e s) le_rfl r

/-- Actual normalization pullback retains the entire original tensor
coordinate value in its original fraction field. -/
theorem extendedClosedGaussNormalizedChartSectionValue_pencil_pullback (r : Γ(P, Uₚ)) :
    extendedClosedGaussNormalizedChartSectionValue H I E hH e s (extendedClosedGaussNormalizationChartPullback H I E hH e s r) =
      algebraMap T₀ (FractionRing T₀)
        (extendedClosedGaussPencilTensorChartSectionEquiv H I E hH e s r) := by
  exact (congrArg (algebraMap N₀ (FractionRing T₀))
    (extendedClosedGaussNormalizedChartSectionEquiv_pencil_pullback H I E hH e s r)).trans
      (IsScalarTower.algebraMap_apply T₀ N₀ (FractionRing T₀) _).symm

/-- The original tensor chart embeds in the normalized pencil's own
function field through the actual normalized affine section identification. -/
noncomputable def extendedClosedGaussTensorChartToOwnFunctionField : T₀ →+* (N).functionField :=
  (extendedClosedGaussNormalizedChartFunctionFieldEquiv H I E hH e s).toRingHom.comp
    (algebraMap T₀ (FractionRing T₀))

/-- The original tensor-chart embedding is the actual generic germ
of normalization pullback on every original pencil-chart regular section. -/
theorem extendedClosedGaussTensorChartToOwnFunctionField_pencil_section (r : Γ(P, Uₚ)) :
    extendedClosedGaussTensorChartToOwnFunctionField H I E hH e s
        (extendedClosedGaussPencilTensorChartSectionEquiv H I E hH e s r) =
      (N).germToFunctionField Uₙ (extendedClosedGaussNormalizationChartPullback H I E hH e s r) := by
  exact (congrArg (extendedClosedGaussNormalizedChartFunctionFieldEquiv H I E hH e s)
    (extendedClosedGaussNormalizedChartSectionValue_pencil_pullback H I E hH e s r).symm).trans
      (extendedClosedGaussNormalizedChartFunctionFieldEquiv_section H I E hH e s
        (extendedClosedGaussNormalizationChartPullback H I E hH e s r))

end DimensionFourDependence
