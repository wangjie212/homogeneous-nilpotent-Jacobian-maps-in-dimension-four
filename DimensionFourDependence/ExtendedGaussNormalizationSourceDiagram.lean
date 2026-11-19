import DimensionFourDependence.ExtendedGaussPencilSourceDiagram
import DimensionFourDependence.ExtendedGaussNormalizationMorphism
import DimensionFourDependence.AffineCoordinateMorphism

/-! # The global normalized source projection retains the original source map

The normalization chart maps to the actual pencil chart by its original
normalization ring inclusion. Its actual global projection to the
original projective source is the original source-section map used by
the tensor-normalization local models.
-/

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
local notation "S₀" => projectiveCoordinateChartAlgebra (C := C₀)
  (rationalCoordinate (K := K) (n := 4)) (s.symm none)
local notation "T₀" => S₀ ⊗[C₀] E
local notation "N₀" => normalizationRing T₀
local notation "Uₖ" => Proj.basicOpen (homogeneousSubmodule (Fin 4) K) (X (s.symm none))
local notation "hUₖ" => Proj.isAffineOpen_basicOpen (homogeneousSubmodule (Fin 4) K)
  (X (s.symm none)) (isHomogeneous_X (R := K) _) (by omega)

/-- The actual pencil tensor chart inclusion is induced by its actual
affine section-coordinate isomorphism. -/
theorem extendedClosedGaussPencilTensorChartInclusion_fromSpec :
    extendedClosedGaussPencilTensorChartInclusion H I E hH e s =
      Spec.map (CommRingCat.ofHom
        (extendedClosedGaussPencilTensorChartSectionEquiv H I E hH e s).toRingHom) ≫
      (extendedClosedGaussPencilChartOpen_isAffineOpen H I E hH e s).fromSpec := by
  have h := affineOpenChartSectionEquiv_to_base
    (extendedClosedGaussPencilChartOpen H I E hH e s)
    (extendedClosedGaussPencilChartOpen_isAffineOpen H I E hH e s)
    (CommRingCat.of T₀) (extendedClosedGaussPencilTensorChartIso H I E hH e s)
  convert! h using 1

/-- The actual global normalization restricted to the original tensor
chart is precisely the original coordinate normalization map. -/
theorem extendedClosedGaussNormalizationTensorChartInclusion_to_pencil_chart :
    extendedClosedGaussNormalizationTensorChartInclusion H I E hH e s ≫
        extendedClosedGaussNormalizationSchemeMap H I E hH e =
      Spec.map (CommRingCat.ofHom (algebraMap T₀ N₀)) ≫
        extendedClosedGaussPencilTensorChartInclusion H I E hH e s := by
  let normMap : CommRingCat.of T₀ ⟶ CommRingCat.of N₀ := CommRingCat.ofHom (algebraMap T₀ N₀)
  let coordinateMap : Γ(extendedClosedGaussPencilScheme H I E hH e,
      extendedClosedGaussPencilChartOpen H I E hH e s) ⟶ CommRingCat.of T₀ :=
    CommRingCat.ofHom (extendedClosedGaussPencilTensorChartSectionEquiv H I E hH e s).toRingHom
  have hn := extendedClosedGaussNormalizationTensorChartInclusion_to_base H I E hH e s
  have hp := extendedClosedGaussPencilTensorChartInclusion_fromSpec H I E hH e s
  calc
    _ = Spec.map (coordinateMap ≫ normMap) ≫
        (extendedClosedGaussPencilChartOpen_isAffineOpen H I E hH e s).fromSpec := by
      convert! hn using 1
    _ = Spec.map normMap ≫ Spec.map coordinateMap ≫
        (extendedClosedGaussPencilChartOpen_isAffineOpen H I E hH e s).fromSpec := by
      rw [Spec.map_comp, Category.assoc]
    _ = _ := by
      have h := congrArg (fun f => Spec.map normMap ≫ f) hp.symm
      convert! h using 1

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The actual global projection from the extended normalization to
the original projective source is the original source-section inclusion
in the original tensor-normalization coordinate chart. -/
theorem extendedClosedGaussNormalizationTensorChartInclusion_to_source :
    extendedClosedGaussNormalizationTensorChartInclusion H I E hH e s ≫
        extendedClosedGaussNormalizationSourceMorphism H I E hH e =
      Spec.map (CommRingCat.ofHom
        ((algebraMap T₀ N₀).comp (extendedClosedGaussProjectiveSourceSectionHom H I E s))) ≫
        (hUₖ).fromSpec := by
  have h := congrArg (fun f => f ≫ extendedClosedGaussPencilSourceMorphism H I E hH e)
    (extendedClosedGaussNormalizationTensorChartInclusion_to_pencil_chart H I E hH e s)
  simp only [Category.assoc] at h
  rw [extendedClosedGaussPencilTensorChartInclusion_to_source, ← Spec.map_comp_assoc] at h
  unfold extendedClosedGaussNormalizationSourceMorphism
  convert! h using 1

end DimensionFourDependence
