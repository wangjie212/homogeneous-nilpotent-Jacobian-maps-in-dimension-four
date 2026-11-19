import DimensionFourDependence.ClosedGaussNormalizationSchemeCharts

/-! # A finite original-coordinate affine atlas of the global normalization

The canonical normalized ratio rings and their actual chart inclusions
are assembled into a four-chart affine open cover of the constructed
global normalized pencil.
-/

namespace DimensionFourDependence

open AlgebraicGeometry CategoryTheory TopologicalSpace.Opens

universe u

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {K : Type u} [Field K] [CharZero K]
  (H : Fin 4 → MvPolynomial (Fin 4) K) {d : ℕ} (hH : IsHomogMap H d)
  (I : ImageRelationWitness H) (e : RatFunc K ≃ₐ[K] closedGaussParameterField H I)

/-- Each actual normalized chart inclusion has precisely the original
inverse-coordinate open as its range. -/
theorem closedGaussNormalizationSchemeChartInclusion_opensRange (a : Fin 4) :
    letI : IsOpenImmersion (closedGaussNormalizationSchemeChartInclusion H hH I e a) :=
      closedGaussNormalizationSchemeChartInclusion_isOpenImmersion H hH I e a
    (closedGaussNormalizationSchemeChartInclusion H hH I e a).opensRange =
      closedGaussNormalizationSchemeChartOpen H hH I e a := by
  let : IsOpenImmersion (closedGaussNormalizationSchemeChartInclusion H hH I e a) :=
    closedGaussNormalizationSchemeChartInclusion_isOpenImmersion H hH I e a
  change ((closedGaussNormalizationSchemeChartIso H hH I e a).inv ≫
    (closedGaussNormalizationSchemeChartOpen H hH I e a).ι).opensRange = _
  exact (Scheme.Hom.opensRange_comp_of_isIso _ _).trans
    (closedGaussNormalizationSchemeChartOpen H hH I e a).opensRange_ι

/-- The canonical normalizations of the four original ratio rings,
with their actual inclusions, form an affine atlas of the global pencil normalization. -/
noncomputable def closedGaussNormalizationSchemeOriginalAffineCover :
    (closedGaussPencilNormalizationScheme H hH I e).AffineOpenCover := by
  let N := closedGaussPencilNormalizationScheme H hH I e
  let A (a : Fin 4) := CommRingCat.of (normalizationRing
    (projectiveCoordinateChartAlgebra (C := closedGaussParameterField H I)
      (rationalCoordinate (K := K) (n := 4)) a))
  let j (a : Fin 4) : Spec (A a) ⟶ N := closedGaussNormalizationSchemeChartInclusion H hH I e a
  let hopen (a : Fin 4) : IsOpenImmersion (j a) :=
    closedGaussNormalizationSchemeChartInclusion_isOpenImmersion H hH I e a
  let idx (y : N) := (mem_iSup.mp ((closedGaussNormalizationSchemeChartOpen_iSup H hH I e).ge
    (show y ∈ ⊤ from trivial))).choose
  refine { I₀ := Fin 4, X := A, f := j, map_prop := hopen, idx := idx, covers := ?_ }
  intro y
  let : IsOpenImmersion (j (idx y)) := hopen _
  have hmem : y ∈ closedGaussNormalizationSchemeChartOpen H hH I e (idx y) :=
    (mem_iSup.mp ((closedGaussNormalizationSchemeChartOpen_iSup H hH I e).ge
      (show y ∈ ⊤ from trivial))).choose_spec
  exact (closedGaussNormalizationSchemeChartInclusion_opensRange H hH I e (idx y)).ge hmem

end DimensionFourDependence
