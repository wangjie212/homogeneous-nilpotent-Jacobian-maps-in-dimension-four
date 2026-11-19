import DimensionFourDependence.ExtendedGaussSchemeTensorCharts

/-! # Four original tensor-normalization charts cover the extended global scheme

The same original coordinate rings tensor the new field, normalized
after tensoring, form an actual four-chart affine atlas of the global
normalization constructed after coefficient extension.
-/

namespace DimensionFourDependence

open MvPolynomial AlgebraicGeometry CategoryTheory TopologicalSpace.Opens
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

/-- The four original tensor coordinate charts cover the extended pencil scheme. -/
theorem extendedClosedGaussPencilChartOpen_iSup :
    ⨆ a : Fin 4, extendedClosedGaussPencilChartOpen H I E hH e (finSuccEquiv' a) = ⊤ := by
  let 𝒢 := homogeneousSubmodule (Fin 4) E
  have hgen : Algebra.adjoin (𝒢 0) (Set.range (X : Fin 4 → MvPolynomial (Fin 4) E)) = ⊤ := by
    let S := Algebra.adjoin (𝒢 0) (Set.range (X : Fin 4 → MvPolynomial (Fin 4) E))
    apply top_unique
    intro P hP
    clear hP
    induction P using MvPolynomial.induction_on with
    | C c => exact S.algebraMap_mem ⟨MvPolynomial.C c, isHomogeneous_C (Fin 4) c⟩
    | add P Q hP hQ => exact S.add_mem hP hQ
    | mul_X P i hP => exact S.mul_mem hP (Algebra.subset_adjoin ⟨i, rfl⟩)
  have hcover := Proj.iSup_basicOpen_eq_top' 𝒢 (X : Fin 4 → MvPolynomial (Fin 4) E)
    (fun i => ⟨1, isHomogeneous_X (R := E) i⟩) hgen
  unfold extendedClosedGaussPencilChartOpen
  simp only [finSuccEquiv'_symm_none]
  rw [← Scheme.Hom.preimage_iSup, hcover, Scheme.Hom.preimage_top]

/-- The four tensor-normalization inverse charts cover the actual
normalization formed after coefficient extension. -/
theorem extendedClosedGaussNormalizationChartOpen_iSup :
    ⨆ a : Fin 4, extendedClosedGaussNormalizationChartOpen H I E hH e (finSuccEquiv' a) = ⊤ := by
  unfold extendedClosedGaussNormalizationChartOpen
  rw [← Scheme.Hom.preimage_iSup, extendedClosedGaussPencilChartOpen_iSup, Scheme.Hom.preimage_top]

/-- The original tensor-normalization chart inclusion has exactly
its specified inverse-coordinate open as range. -/
theorem extendedClosedGaussNormalizationTensorChartInclusion_opensRange
    (s : Fin 4 ≃ Option (Fin 3)) :
    letI : IsOpenImmersion (extendedClosedGaussNormalizationTensorChartInclusion H I E hH e s) :=
      extendedClosedGaussNormalizationTensorChartInclusion_isOpenImmersion H I E hH e s
    (extendedClosedGaussNormalizationTensorChartInclusion H I E hH e s).opensRange =
      extendedClosedGaussNormalizationChartOpen H I E hH e s := by
  let : IsOpenImmersion (extendedClosedGaussNormalizationTensorChartInclusion H I E hH e s) :=
    extendedClosedGaussNormalizationTensorChartInclusion_isOpenImmersion H I E hH e s
  change ((extendedClosedGaussNormalizationTensorChartIso H I E hH e s).inv ≫
    (extendedClosedGaussNormalizationChartOpen H I E hH e s).ι).opensRange = _
  exact (Scheme.Hom.opensRange_comp_of_isIso _ _).trans
    (extendedClosedGaussNormalizationChartOpen H I E hH e s).opensRange_ι

/-- An actual four-chart affine atlas whose rings are the original
canonical tensor normalizations used in the local order results. -/
noncomputable def extendedClosedGaussNormalizationTensorAffineCover :
    (extendedClosedGaussNormalizationScheme H I E hH e).AffineOpenCover := by
  let N := extendedClosedGaussNormalizationScheme H I E hH e
  let A (a : Fin 4) := CommRingCat.of (normalizationRing
    (projectiveCoordinateChartAlgebra (C := closedGaussParameterField H I)
      (rationalCoordinate (K := K) (n := 4)) ((finSuccEquiv' a).symm none) ⊗[closedGaussParameterField H I] E))
  let j (a : Fin 4) : Spec (A a) ⟶ N :=
    extendedClosedGaussNormalizationTensorChartInclusion H I E hH e (finSuccEquiv' a)
  let hopen (a : Fin 4) : IsOpenImmersion (j a) :=
    extendedClosedGaussNormalizationTensorChartInclusion_isOpenImmersion H I E hH e (finSuccEquiv' a)
  let idx (y : N) := (mem_iSup.mp ((extendedClosedGaussNormalizationChartOpen_iSup H I E hH e).ge
    (show y ∈ ⊤ from trivial))).choose
  refine { I₀ := Fin 4, X := A, f := j, map_prop := hopen, idx := idx, covers := ?_ }
  intro y
  let : IsOpenImmersion (j (idx y)) := hopen _
  have hmem : y ∈ extendedClosedGaussNormalizationChartOpen H I E hH e (finSuccEquiv' (idx y)) :=
    (mem_iSup.mp ((extendedClosedGaussNormalizationChartOpen_iSup H I E hH e).ge
      (show y ∈ ⊤ from trivial))).choose_spec
  exact (extendedClosedGaussNormalizationTensorChartInclusion_opensRange H I E hH e
    (finSuccEquiv' (idx y))).ge hmem

end DimensionFourDependence
