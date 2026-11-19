import DimensionFourDependence.ExtendedGaussProjectiveSections

/-! # The actual global pencil source projection in original tensor coordinates

The original tensor chart's global inclusion followed by the actual
original projective source projection is the spectrum morphism of the
specified original-source section map.
-/

namespace DimensionFourDependence

open MvPolynomial AlgebraicGeometry CategoryTheory
open scoped TensorProduct

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {K : Type u} [Field K] [CharZero K]
  (H : Fin 4 → MvPolynomial (Fin 4) K) (I : ImageRelationWitness H)
  (E : Type u) [Field E] [Algebra (closedGaussParameterField H I) E]
  [Algebra.IsAlgebraic (closedGaussParameterField H I) E]
  {d : ℕ} (hH : IsHomogMap H d)
  (e : RatFunc K ≃ₐ[K] closedGaussParameterField H I)
  (s : Fin 4 ≃ Option (Fin 3))

local notation "C₀" => closedGaussParameterField H I
local notation "zₑ" => primeQuotientCoordinate (extendedClosedGaussPencilIdeal H I E)
local notation "S₀" => projectiveCoordinateChartAlgebra (C := C₀)
  (rationalCoordinate (K := K) (n := 4)) (s.symm none)
local notation "Sₑ" => projectiveCoordinateChartAlgebra (C := E) zₑ (s.symm none)
local notation "Uₖ" => Proj.basicOpen (homogeneousSubmodule (Fin 4) K) (X (s.symm none))
local notation "Uₑ" => Proj.basicOpen (homogeneousSubmodule (Fin 4) E) (X (s.symm none))
local notation "hUₖ" => Proj.isAffineOpen_basicOpen (homogeneousSubmodule (Fin 4) K)
  (X (s.symm none)) (isHomogeneous_X (R := K) _) (by omega)
local notation "hUₑ" => Proj.isAffineOpen_basicOpen (homogeneousSubmodule (Fin 4) E)
  (X (s.symm none)) (isHomogeneous_X (R := E) _) (by omega)

/-- The original tensor coordinate chart's actual global pencil inclusion. -/
noncomputable def extendedClosedGaussPencilTensorChartInclusion :
    Spec (CommRingCat.of (S₀ ⊗[C₀] E)) ⟶ extendedClosedGaussPencilScheme H I E hH e :=
  (extendedClosedGaussPencilTensorChartIso H I E hH e s).inv ≫
    (extendedClosedGaussPencilChartOpen H I E hH e s).ι

/-- The original tensor coordinate chart embeds as an actual open. -/
theorem extendedClosedGaussPencilTensorChartInclusion_isOpenImmersion :
    IsOpenImmersion (extendedClosedGaussPencilTensorChartInclusion H I E hH e s) := by
  unfold extendedClosedGaussPencilTensorChartInclusion
  infer_instance

/-- The actual global source projection from the extended pencil is
the specified original source-section map in its original tensor chart. -/
theorem extendedClosedGaussPencilTensorChartInclusion_to_source :
    extendedClosedGaussPencilTensorChartInclusion H I E hH e s ≫
        extendedClosedGaussPencilSourceMorphism H I E hH e =
      Spec.map (CommRingCat.ofHom (extendedClosedGaussProjectiveSourceSectionHom H I E s)) ≫
        (hUₖ).fromSpec := by
  set_option backward.isDefEq.respectTransparency true in
  set_option backward.isDefEq.respectTransparency.types true in
  exact by
    let b := extendedClosedGaussRatioCoordinateEquiv H I E hH e s
    let bIso : CommRingCat.of (S₀ ⊗[C₀] E) ≅ CommRingCat.of Sₑ := b.toCommRingCatIso
    let bMap := bIso.inv
    let σ := polynomialProjectiveCoefficientMap (extendedClosedGaussSourceCoefficientHom H I E)
    let hU : Uₑ ≤ σ ⁻¹ᵁ Uₖ :=
      le_of_eq (polynomialProjectiveCoefficientMap_preimage_basicOpen
        (extendedClosedGaussSourceCoefficientHom H I E) (s.symm none)).symm
    let p := extendedClosedGaussPencilGenericPoint H I E hH e
    let ha := extendedClosedGaussRatioCoordinate_ne_zero H I E (s.symm none)
    set_option backward.isDefEq.respectTransparency false in
    set_option backward.isDefEq.respectTransparency.types false in
    let ambientMap : Γ(AlgebraicGeometry.Proj (homogeneousSubmodule (Fin 4) E), Uₑ) ⟶
        CommRingCat.of Sₑ := CommRingCat.ofHom (projectiveAmbientSectionToSource zₑ (s.symm none) ha)
    set_option backward.isDefEq.respectTransparency false in
    set_option backward.isDefEq.respectTransparency.types false in
    let sourceMap : Γ(AlgebraicGeometry.Proj (homogeneousSubmodule (Fin 4) K), Uₖ) ⟶
        CommRingCat.of (S₀ ⊗[C₀] E) :=
      CommRingCat.ofHom (extendedClosedGaussProjectiveSourceSectionHom H I E s)
    have hrel : p.asHomogeneousIdeal.toIdeal = RingHom.ker (aeval zₑ).toRingHom :=
      (extendedClosedGaussRatioCoordinate_relations H I E).symm
    have hbase := projectiveSourceReducedClosureAffineChart_inv_to_ambient (C := E)
      zₑ (s.symm none) ha p hrel (extendedClosedGaussPencilIdeal_X_not_mem H I E _)
    have h := congrArg (fun k => Spec.map bMap ≫ k ≫ σ) hbase
    simp only [Category.assoc] at h
    rw [← IsAffineOpen.SpecMap_appLE_fromSpec σ (hUₖ) (hUₑ) hU,
      ← Spec.map_comp_assoc, ← Spec.map_comp_assoc] at h
    have hc : σ.appLE Uₖ Uₑ hU ≫ ambientMap = sourceMap ≫ bIso.hom := by
      apply CommRingCat.hom_ext
      apply RingHom.ext
      intro r
      exact (extendedClosedGaussProjectiveSourceSectionHom_compatibility H I E hH e s r).symm
    have hb : σ.appLE Uₖ Uₑ hU ≫ ambientMap ≫ bMap = sourceMap := by
      rw [← Category.assoc, hc, Category.assoc, Iso.hom_inv_id, Category.comp_id]
    have h' := h.trans (congrArg (fun f => Spec.map f ≫ (hUₖ).fromSpec) hb)
    unfold extendedClosedGaussPencilTensorChartInclusion extendedClosedGaussPencilSourceMorphism
    convert! h' using 1

end DimensionFourDependence
