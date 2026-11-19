import DimensionFourDependence.ClosedGaussPencilSchemeCharts

/-! # Original unnormalized tensor-source pencil affine cover -/

namespace DimensionFourDependence

open MvPolynomial AlgebraicGeometry CategoryTheory TopologicalSpace.Opens

universe u

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {K : Type u} [Field K] [CharZero K]
  (H : Fin 4 → MvPolynomial (Fin 4) K) {d : ℕ} (hH : IsHomogMap H d)
  (I : ImageRelationWitness H) (e : RatFunc K ≃ₐ[K] closedGaussParameterField H I)

/-- The actual four original ratio charts of the unnormalized pencil
form an affine open cover, in the same coordinate indexing as the extended charts. -/
noncomputable def closedGaussPencilOriginalAffineCover :
    (closedGaussPencilScheme H hH I e).AffineOpenCover := by
  let Q := closedGaussPencilScheme H hH I e
  let U (a : Fin 4) := closedGaussPencilSchemeChartOpen H hH I e ((finSuccEquiv' a).symm none)
  let A (a : Fin 4) := CommRingCat.of (projectiveCoordinateChartAlgebra
    (C := closedGaussParameterField H I) (rationalCoordinate (K := K) (n := 4))
      ((finSuccEquiv' a).symm none))
  let j (a : Fin 4) : Spec (A a) ⟶ Q :=
    (closedGaussPencilSchemeChartIso H hH I e ((finSuccEquiv' a).symm none)).inv ≫ (U a).ι
  have hcover : ⨆ a, U a = ⊤ := by
    simpa only [U, finSuccEquiv'_symm_none] using closedGaussPencilSchemeChartOpen_iSup H hH I e
  let idx (y : Q) := (mem_iSup.mp (hcover.ge (show y ∈ ⊤ from trivial))).choose
  refine { I₀ := Fin 4, X := A, f := j, map_prop := fun _ => inferInstance, idx := idx, covers := ?_ }
  intro y
  have hmem : y ∈ U (idx y) := (mem_iSup.mp (hcover.ge (show y ∈ ⊤ from trivial))).choose_spec
  change y ∈ (j (idx y)).opensRange
  rw [Scheme.Hom.opensRange_comp_of_isIso]
  simpa only [Scheme.Opens.opensRange_ι] using hmem

end DimensionFourDependence
