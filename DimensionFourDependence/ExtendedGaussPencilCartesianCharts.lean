import DimensionFourDependence.ExtendedGaussPencilChartBaseMaps
import DimensionFourDependence.SchemeBaseChangeCharts

/-! # The original pencil charts are actual Cartesian coefficient squares -/

namespace DimensionFourDependence

open MvPolynomial AlgebraicGeometry CategoryTheory
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
local notation "S₀" => projectiveCoordinateChartAlgebra (C := C₀)
  (rationalCoordinate (K := K) (n := 4)) (s.symm none)
local notation "j₀" => closedGaussPencilChartInclusion H I hH e s
local notation "jₑ" => extendedClosedGaussPencilTensorChartInclusion H I E hH e s
local notation "m" => extendedClosedGaussPencilToOriginal H I E hH e
local notation "l" => Spec.map (CommRingCat.ofHom
  (Algebra.TensorProduct.includeLeftRingHom : S₀ →+* S₀ ⊗[C₀] E))

/-- The original pencil's actual source chart is an open immersion. -/
theorem closedGaussPencilChartInclusion_isOpenImmersion : IsOpenImmersion j₀ := by
  unfold closedGaussPencilChartInclusion
  infer_instance

/-- Its open range is its specified original coordinate open. -/
theorem closedGaussPencilChartInclusion_opensRange :
    letI : IsOpenImmersion j₀ := closedGaussPencilChartInclusion_isOpenImmersion H I hH e s
    (j₀).opensRange = closedGaussPencilSchemeChartOpen H hH I e (s.symm none) := by
  let : IsOpenImmersion j₀ := closedGaussPencilChartInclusion_isOpenImmersion H I hH e s
  unfold closedGaussPencilChartInclusion
  rw [Scheme.Hom.opensRange_comp_of_isIso, Scheme.Opens.opensRange_ι]

/-- The actual tensor chart has exactly its specified extended open as range. -/
theorem extendedClosedGaussPencilTensorChartInclusion_opensRange :
    letI : IsOpenImmersion jₑ := extendedClosedGaussPencilTensorChartInclusion_isOpenImmersion H I E hH e s
    (jₑ).opensRange = extendedClosedGaussPencilChartOpen H I E hH e s := by
  let : IsOpenImmersion jₑ := extendedClosedGaussPencilTensorChartInclusion_isOpenImmersion H I E hH e s
  unfold extendedClosedGaussPencilTensorChartInclusion
  rw [Scheme.Hom.opensRange_comp_of_isIso, Scheme.Opens.opensRange_ι]

/-- The extended tensor chart is the actual inverse-image open of
the original-pencil coordinate chart under the actual original-pencil map. -/
theorem extendedClosedGaussPencilTensorChart_original_isPullback :
    IsPullback (jₑ) (l) (m) (j₀) := by
  let : IsOpenImmersion j₀ := closedGaussPencilChartInclusion_isOpenImmersion H I hH e s
  let : IsOpenImmersion jₑ := extendedClosedGaussPencilTensorChartInclusion_isOpenImmersion H I E hH e s
  have hcomm : (jₑ) ≫ (m) = (l) ≫ (j₀) :=
    extendedClosedGaussPencilTensorChartInclusion_to_original H I E hH e s
  have hrange : (m) ⁻¹ᵁ (j₀).opensRange = (jₑ).opensRange := by
    rw [closedGaussPencilChartInclusion_opensRange, extendedClosedGaussPencilTensorChartInclusion_opensRange,
      extendedClosedGaussPencilToOriginal_preimage_chart]
  have hresult := IsOpenImmersion.isPullback
    (U := Spec (CommRingCat.of (S₀ ⊗[C₀] E))) (V := Spec (CommRingCat.of S₀))
    (X := extendedClosedGaussPencilScheme H I E hH e) (Y := closedGaussPencilScheme H hH I e)
    (l) (jₑ) (j₀) (m) hcomm hrange
  exact hresult.flip

/-- Both actual structure maps make each original tensor chart the
categorical affine coefficient base change of the original-pencil chart. -/
theorem extendedClosedGaussPencilTensorChart_coefficient_isPullback :
    IsPullback (l) ((jₑ) ≫ extendedClosedGaussPencilSchemeToBase H I E hH e)
      ((j₀) ≫ closedGaussPencilSchemeToBase H hH I e)
      (Spec.map (CommRingCat.ofHom (algebraMap C₀ E))) := by
  rw [extendedClosedGaussPencilTensorChartInclusion_to_base, closedGaussPencilChartInclusion_to_base]
  exact spectrum_tensor_coefficient_isPullback C₀ S₀ E

end DimensionFourDependence
