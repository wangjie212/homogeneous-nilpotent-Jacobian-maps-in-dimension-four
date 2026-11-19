import DimensionFourDependence.ExtendedGaussPencilCoefficientSections
import DimensionFourDependence.ExtendedGaussPencilSourceDiagram

/-! # The original-pencil projection is the canonical tensor inclusion on charts -/

namespace DimensionFourDependence

open MvPolynomial AlgebraicGeometry CategoryTheory
open scoped TensorProduct

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 4000000
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
local notation "x₀" => rationalCoordinate (K := K) (n := 4)
local notation "zₑ" => primeQuotientCoordinate (extendedClosedGaussPencilIdeal H I E)
local notation "S₀" => projectiveCoordinateChartAlgebra (C := C₀) x₀ (s.symm none)
local notation "Sₑ" => projectiveCoordinateChartAlgebra (C := E) zₑ (s.symm none)
local notation "U₀" => Proj.basicOpen (homogeneousSubmodule (Fin 4) C₀) (X (s.symm none))
local notation "Uₑ" => Proj.basicOpen (homogeneousSubmodule (Fin 4) E) (X (s.symm none))
local notation "hU₀" => Proj.isAffineOpen_basicOpen (homogeneousSubmodule (Fin 4) C₀)
  (X (s.symm none)) (isHomogeneous_X (R := C₀) _) (by omega)
local notation "hUₑ" => Proj.isAffineOpen_basicOpen (homogeneousSubmodule (Fin 4) E)
  (X (s.symm none)) (isHomogeneous_X (R := E) _) (by omega)

/-- The original ratio chart's actual open inclusion into the original pencil. -/
noncomputable def closedGaussPencilChartInclusion :
    Spec (CommRingCat.of S₀) ⟶ closedGaussPencilScheme H hH I e :=
  (closedGaussPencilSchemeChartIso H hH I e (s.symm none)).inv ≫
    (closedGaussPencilSchemeChartOpen H hH I e (s.symm none)).ι

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- The original pencil-chart inclusion retains its ambient source-section map. -/
theorem closedGaussPencilChartInclusion_to_ambient :
    closedGaussPencilChartInclusion H I hH e s ≫ closedGaussPencilSchemeInclusion H hH I e =
      Spec.map (CommRingCat.ofHom (projectiveAmbientSectionToSource (C := C₀)
        x₀ (s.symm none) (source_rationalCoordinate_ne_zero _))) ≫ (hU₀).fromSpec := by
  have h := projectiveSourceReducedClosureAffineChart_inv_to_ambient (C := C₀)
    x₀ (s.symm none) (source_rationalCoordinate_ne_zero _)
    (closedGaussPencilProjectiveGenericPoint H hH I e) rfl
    (closedGaussPencilGenericPoint_mem_chart H hH I e (s.symm none))
  unfold closedGaussPencilChartInclusion
  exact h

/-- In its original tensor coordinates, the actual extended chart's
ambient coefficient projection is induced by the original tensor section map. -/
theorem extendedClosedGaussPencilTensorChartInclusion_to_original_ambient :
    extendedClosedGaussPencilTensorChartInclusion H I E hH e s ≫
        extendedClosedGaussPencilSchemeInclusion H I E hH e ≫
        polynomialProjectiveCoefficientMap (algebraMap C₀ E) =
      Spec.map (CommRingCat.ofHom (extendedClosedGaussPencilAmbientTensorSectionHom H I E s)) ≫
        (hU₀).fromSpec := by
  set_option backward.isDefEq.respectTransparency true in
  set_option backward.isDefEq.respectTransparency.types true in
  exact by
    let b := extendedClosedGaussRatioCoordinateEquiv H I E hH e s
    let bIso : CommRingCat.of (S₀ ⊗[C₀] E) ≅ CommRingCat.of Sₑ := b.toCommRingCatIso
    let bMap := bIso.inv
    let σ := polynomialProjectiveCoefficientMap (algebraMap C₀ E)
    let hU : Uₑ ≤ σ ⁻¹ᵁ U₀ :=
      le_of_eq (polynomialProjectiveCoefficientMap_preimage_basicOpen (algebraMap C₀ E) (s.symm none)).symm
    let p := extendedClosedGaussPencilGenericPoint H I E hH e
    let ha := extendedClosedGaussRatioCoordinate_ne_zero H I E (s.symm none)
    set_option backward.isDefEq.respectTransparency false in
    set_option backward.isDefEq.respectTransparency.types false in
    let ambientMap : Γ(AlgebraicGeometry.Proj (homogeneousSubmodule (Fin 4) E), Uₑ) ⟶
        CommRingCat.of Sₑ := CommRingCat.ofHom (projectiveAmbientSectionToSource zₑ (s.symm none) ha)
    set_option backward.isDefEq.respectTransparency false in
    set_option backward.isDefEq.respectTransparency.types false in
    let sourceMap : Γ(AlgebraicGeometry.Proj (homogeneousSubmodule (Fin 4) C₀), U₀) ⟶
        CommRingCat.of (S₀ ⊗[C₀] E) :=
      CommRingCat.ofHom (extendedClosedGaussPencilAmbientTensorSectionHom H I E s)
    have hrel : p.asHomogeneousIdeal.toIdeal = RingHom.ker (aeval zₑ).toRingHom :=
      (extendedClosedGaussRatioCoordinate_relations H I E).symm
    have hbase := projectiveSourceReducedClosureAffineChart_inv_to_ambient (C := E)
      zₑ (s.symm none) ha p hrel (extendedClosedGaussPencilIdeal_X_not_mem H I E _)
    have h := congrArg (fun k => Spec.map bMap ≫ k ≫ σ) hbase
    simp only [Category.assoc] at h
    rw [← IsAffineOpen.SpecMap_appLE_fromSpec σ (hU₀) (hUₑ) hU,
      ← Spec.map_comp_assoc, ← Spec.map_comp_assoc] at h
    have hc : σ.appLE U₀ Uₑ hU ≫ ambientMap = sourceMap ≫ bIso.hom := by
      apply CommRingCat.hom_ext
      apply RingHom.ext
      intro r
      exact (extendedClosedGaussPencilAmbientTensorSectionHom_compatibility H I E hH e s r).symm
    have hb : σ.appLE U₀ Uₑ hU ≫ ambientMap ≫ bMap = sourceMap := by
      rw [← Category.assoc, hc, Category.assoc, Iso.hom_inv_id, Category.comp_id]
    have h' := h.trans (congrArg (fun f => Spec.map f ≫ (hU₀).fromSpec) hb)
    unfold extendedClosedGaussPencilTensorChartInclusion
    convert! h' using 1

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- The actual global morphism to the original pencil is exactly the
canonical coefficient tensor inclusion in the two original affine charts. -/
theorem extendedClosedGaussPencilTensorChartInclusion_to_original :
    extendedClosedGaussPencilTensorChartInclusion H I E hH e s ≫
        extendedClosedGaussPencilToOriginal H I E hH e =
      Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeLeft : S₀ →ₐ[C₀] S₀ ⊗[C₀] E).toRingHom) ≫
        closedGaussPencilChartInclusion H I hH e s := by
  let : IsClosedImmersion (closedGaussPencilSchemeInclusion H hH I e) :=
    closedGaussPencilSchemeInclusion_isClosedImmersion H hH I e
  rw [← cancel_mono (closedGaussPencilSchemeInclusion H hH I e)]
  simp only [Category.assoc]
  rw [extendedClosedGaussPencilToOriginal_inclusion,
    extendedClosedGaussPencilTensorChartInclusion_to_original_ambient,
    closedGaussPencilChartInclusion_to_ambient, ← Spec.map_comp_assoc]
  rfl

end DimensionFourDependence
