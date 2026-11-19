import DimensionFourDependence.ExtendedGaussPencilSourceDiagram
import DimensionFourDependence.AffineChartSectionNaturality
import DimensionFourDependence.ProjectiveCoordinateRatioEvaluation

/-! # The actual extended projective coordinate pullback in original tensor charts -/

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
local notation "P" => extendedClosedGaussPencilScheme H I E hH e
local notation "Uₚ" => extendedClosedGaussPencilChartOpen H I E hH e s
local notation "Uₑ" => Proj.basicOpen (homogeneousSubmodule (Fin 4) E) (X (s.symm none))
local notation "hUₑ" => Proj.isAffineOpen_basicOpen (homogeneousSubmodule (Fin 4) E)
  (X (s.symm none)) (isHomogeneous_X (R := E) _) (by omega)

/-- Original tensor coordinates of an actual regular section on the
extended ambient projective chart. -/
noncomputable def extendedClosedGaussPencilAmbientSectionHom :
    Γ(AlgebraicGeometry.Proj (homogeneousSubmodule (Fin 4) E), Uₑ) →+* T₀ :=
  (extendedClosedGaussRatioCoordinateEquiv H I E hH e s).symm.toRingHom.comp
    (projectiveAmbientSectionToSource zₑ (s.symm none)
      (extendedClosedGaussRatioCoordinate_ne_zero H I E _))

/-- The original ambient section evaluation as a morphism between
its actual section ring and the original tensor coordinate ring. -/
noncomputable def extendedClosedGaussPencilAmbientSectionMap :
    Γ(AlgebraicGeometry.Proj (homogeneousSubmodule (Fin 4) E), Uₑ) ⟶ CommRingCat.of T₀ :=
  ConcreteCategory.ofHom (C := CommRingCat)
    (extendedClosedGaussPencilAmbientSectionHom H I E hH e s)

/-- The actual projective closed immersion is its original
ambient-section evaluation map on each original tensor affine chart. -/
theorem extendedClosedGaussPencilTensorChartInclusion_to_extended_ambient :
    extendedClosedGaussPencilTensorChartInclusion H I E hH e s ≫
        extendedClosedGaussPencilSchemeInclusion H I E hH e =
      Spec.map (extendedClosedGaussPencilAmbientSectionMap H I E hH e s) ≫
        (hUₑ).fromSpec := by
  let b := extendedClosedGaussRatioCoordinateEquiv H I E hH e s
  let bIso : CommRingCat.of T₀ ≅ CommRingCat.of
      (projectiveCoordinateChartAlgebra (C := E) zₑ (s.symm none)) := b.toCommRingCatIso
  let bMap := bIso.inv
  let p := extendedClosedGaussPencilGenericPoint H I E hH e
  let ha := extendedClosedGaussRatioCoordinate_ne_zero H I E (s.symm none)
  have hrel : p.asHomogeneousIdeal.toIdeal = RingHom.ker (aeval zₑ).toRingHom :=
    (extendedClosedGaussRatioCoordinate_relations H I E).symm
  have hbase := projectiveSourceReducedClosureAffineChart_inv_to_ambient (C := E)
    zₑ (s.symm none) ha p hrel (extendedClosedGaussPencilIdeal_X_not_mem H I E _)
  have h := congrArg (fun k => Spec.map bMap ≫ k) hbase
  rw [← Spec.map_comp_assoc] at h
  unfold extendedClosedGaussPencilTensorChartInclusion
    extendedClosedGaussPencilTensorChartIso extendedClosedGaussPencilAmbientSectionMap
    extendedClosedGaussPencilAmbientSectionHom
  convert! h using 1

/-- Geometric ambient pullback with the original tensor chart as
its explicitly specified target open. -/
noncomputable def extendedClosedGaussPencilAmbientChartPullback :
    Γ(AlgebraicGeometry.Proj (homogeneousSubmodule (Fin 4) E), Uₑ) →+* Γ(P, Uₚ) :=
  ((extendedClosedGaussPencilSchemeInclusion H I E hH e).appLE Uₑ Uₚ le_rfl).hom

/-- The actual ambient section pullback retains its entire original
tensor coordinate value under the actual pencil-chart section identification. -/
theorem extendedClosedGaussPencilTensorChartSectionEquiv_ambient_pullback
    (r : Γ(AlgebraicGeometry.Proj (homogeneousSubmodule (Fin 4) E), Uₑ)) :
    extendedClosedGaussPencilTensorChartSectionEquiv H I E hH e s
        (extendedClosedGaussPencilAmbientChartPullback H I E hH e s r) =
      extendedClosedGaussPencilAmbientSectionHom H I E hH e s r :=
  affineChartSectionEquiv_pullback Uₚ (CommRingCat.of T₀)
    (extendedClosedGaussPencilTensorChartIso H I E hH e s)
    (extendedClosedGaussPencilSchemeInclusion H I E hH e)
    ⟨Uₑ, hUₑ⟩ (extendedClosedGaussPencilAmbientSectionMap H I E hH e s)
    (extendedClosedGaussPencilTensorChartInclusion_to_extended_ambient H I E hH e s) le_rfl r

/-- Actual regular original coordinate sections pull back to the
original tensor coordinate ratios, with the specified ratio-ring identification. -/
theorem extendedClosedGaussPencilAmbientSectionHom_coordinate (i : Fin 4) :
    extendedClosedGaussPencilAmbientSectionHom H I E hH e s
        (projectiveCoordinateRatioSection E (s.symm none) i) =
      (extendedClosedGaussRatioCoordinateEquiv H I E hH e s).symm
        (projectiveChartTransition (C := E) zₑ (s.symm none) i) :=
  congrArg (extendedClosedGaussRatioCoordinateEquiv H I E hH e s).symm
    (projectiveCoordinateRatioSection_source_transition zₑ (s.symm none)
      (extendedClosedGaussRatioCoordinate_ne_zero H I E _) i)

end DimensionFourDependence
