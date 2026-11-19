import DimensionFourDependence.ExtendedGaussPencilOriginalChartMap
import DimensionFourDependence.ProjectiveChartBaseMap
import DimensionFourDependence.ExtendedGaussPencilBaseChangeComparison

/-! # Both pencil chart structure maps are the specified coefficient maps -/

namespace DimensionFourDependence

open MvPolynomial AlgebraicGeometry CategoryTheory
open scoped TensorProduct

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 4000000
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
local notation "x₀" => rationalCoordinate (K := K) (n := 4)
local notation "zₑ" => primeQuotientCoordinate (extendedClosedGaussPencilIdeal H I E)
local notation "S₀" => projectiveCoordinateChartAlgebra (C := C₀) x₀ (s.symm none)
local notation "Sₑ" => projectiveCoordinateChartAlgebra (C := E) zₑ (s.symm none)

/-- The original pencil chart has exactly its original coefficient
structure map, in its original source-ratio coordinate ring. -/
theorem closedGaussPencilChartInclusion_to_base :
    closedGaussPencilChartInclusion H I hH e s ≫ closedGaussPencilSchemeToBase H hH I e =
      Spec.map (CommRingCat.ofHom (algebraMap C₀ S₀)) := by
  unfold closedGaussPencilSchemeToBase
  rw [← Category.assoc, closedGaussPencilChartInclusion_to_ambient,
    Category.assoc, projective_ratio_chart_to_base]

/-- The actual tensor chart's projection to the extended field is
the canonical right tensor inclusion, with no coordinate-map hypothesis. -/
theorem extendedClosedGaussPencilTensorChartInclusion_to_base :
    extendedClosedGaussPencilTensorChartInclusion H I E hH e s ≫
        extendedClosedGaussPencilSchemeToBase H I E hH e =
      Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight : E →ₐ[C₀] S₀ ⊗[C₀] E).toRingHom) := by
  let b := extendedClosedGaussRatioCoordinateEquiv H I E hH e s
  let bIso : CommRingCat.of (S₀ ⊗[C₀] E) ≅ CommRingCat.of Sₑ := b.toCommRingCatIso
  let bMap := bIso.inv
  let p := extendedClosedGaussPencilGenericPoint H I E hH e
  let ha := extendedClosedGaussRatioCoordinate_ne_zero H I E (s.symm none)
  have hrel : p.asHomogeneousIdeal.toIdeal = RingHom.ker (aeval zₑ).toRingHom :=
    (extendedClosedGaussRatioCoordinate_relations H I E).symm
  have hbase := projectiveSourceReducedClosureAffineChart_inv_to_ambient (C := E)
    zₑ (s.symm none) ha p hrel (extendedClosedGaussPencilIdeal_X_not_mem H I E _)
  have h := congrArg (fun k => Spec.map bMap ≫ k ≫ polynomialProjectiveToBase E) hbase
  simp only [Category.assoc] at h
  rw [projective_ratio_chart_to_base, ← Spec.map_comp] at h
  have hb : CommRingCat.ofHom (algebraMap E Sₑ) ≫ bMap =
      CommRingCat.ofHom (Algebra.TensorProduct.includeRight : E →ₐ[C₀] S₀ ⊗[C₀] E).toRingHom := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro c
    change b.symm (algebraMap E Sₑ c) = (1 : S₀) ⊗ₜ[C₀] c
    apply b.injective
    rw [b.apply_symm_apply]
    exact (extendedClosedGaussRatioCoordinateEquiv_tmul_coefficient H I E hH e s c).symm
  have h' := h.trans (congrArg (fun k => Spec.map k) hb)
  unfold extendedClosedGaussPencilTensorChartInclusion extendedClosedGaussPencilSchemeToBase
  convert! h' using 1

end DimensionFourDependence
