import DimensionFourDependence.ClosedGaussPencilSchemeCharts
import DimensionFourDependence.ClosedGaussPencilNormalizationScheme
import DimensionFourDependence.NormalizationAffineCoordinateChart

/-! # Actual normalized ratio charts and their global scheme stalks

The global pencil normalization's inverse standard opens are the
canonical normalizations of the existing original source-ratio rings.
These four actual affine opens cover the global normalization. A prime
of one of those rings gives a point whose global stalk is its original
prime localization.
-/

namespace DimensionFourDependence

open MvPolynomial AlgebraicGeometry CategoryTheory

universe u

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {K : Type u} [Field K] [CharZero K]
  (H : Fin 4 → MvPolynomial (Fin 4) K) {d : ℕ} (hH : IsHomogMap H d)
  (I : ImageRelationWitness H) (e : RatFunc K ≃ₐ[K] closedGaussParameterField H I)

local notation "Rₐ" a:max => projectiveCoordinateChartAlgebra (C := closedGaussParameterField H I)
  (rationalCoordinate (K := K) (n := 4)) a

/-- The actual inverse standard affine open on the global normalization. -/
noncomputable def closedGaussNormalizationSchemeChartOpen (a : Fin 4) :
    (closedGaussPencilNormalizationScheme H hH I e).Opens :=
  closedGaussPencilNormalizationSchemeMap H hH I e ⁻¹ᵁ closedGaussPencilSchemeChartOpen H hH I e a

/-- The inverse original-coordinate open in the actual global normalization
is the canonical normalization of the original ratio ring. -/
noncomputable def closedGaussNormalizationSchemeChartIso (a : Fin 4) :
    (closedGaussNormalizationSchemeChartOpen H hH I e a).toScheme ≅
      Spec (CommRingCat.of (normalizationRing (Rₐ a))) := by
  let : IsIntegral (closedGaussPencilScheme H hH I e) := closedGaussPencilScheme_isIntegral H hH I e
  let : Nonempty (closedGaussPencilSchemeChartOpen H hH I e a) :=
    closedGaussPencilSchemeChartOpen_nonempty H hH I e a
  exact integralSchemeNormalizationCoordinateChart (closedGaussPencilScheme H hH I e)
    ⟨closedGaussPencilSchemeChartOpen H hH I e a, closedGaussPencilSchemeChartOpen_isAffineOpen H hH I e a⟩
    (Rₐ a) (closedGaussPencilSchemeChartSectionEquiv H hH I e a)

/-- These actual inverse ratio charts are affine opens of the global normalization. -/
theorem closedGaussNormalizationSchemeChartOpen_isAffineOpen (a : Fin 4) :
    IsAffineOpen (closedGaussNormalizationSchemeChartOpen H hH I e a) :=
  IsAffine.of_isIso (closedGaussNormalizationSchemeChartIso H hH I e a).hom

/-- All four original-coordinate normalized charts cover the actual global normalization. -/
theorem closedGaussNormalizationSchemeChartOpen_iSup :
    ⨆ a : Fin 4, closedGaussNormalizationSchemeChartOpen H hH I e a = ⊤ := by
  unfold closedGaussNormalizationSchemeChartOpen
  rw [← Scheme.Hom.preimage_iSup, closedGaussPencilSchemeChartOpen_iSup, Scheme.Hom.preimage_top]

/-- The actual chart open immersion from the original canonical normalization ring. -/
noncomputable def closedGaussNormalizationSchemeChartInclusion (a : Fin 4) :
    Spec (CommRingCat.of (normalizationRing (Rₐ a))) ⟶ closedGaussPencilNormalizationScheme H hH I e :=
  (closedGaussNormalizationSchemeChartIso H hH I e a).inv ≫
    (closedGaussNormalizationSchemeChartOpen H hH I e a).ι

/-- The original normalized coordinate chart is an actual open immersion. -/
theorem closedGaussNormalizationSchemeChartInclusion_isOpenImmersion (a : Fin 4) :
    IsOpenImmersion (closedGaussNormalizationSchemeChartInclusion H hH I e a) := by
  unfold closedGaussNormalizationSchemeChartInclusion
  infer_instance

/-- The actual point of the global normalization determined by an
original normalized ratio-ring prime. -/
@[irreducible] noncomputable def closedGaussNormalizationSchemeChartPoint
    (a : Fin 4) (q : PrimeSpectrum (normalizationRing (Rₐ a))) :
    closedGaussPencilNormalizationScheme H hH I e :=
  let j : Spec (CommRingCat.of (normalizationRing (Rₐ a))) ⟶
      closedGaussPencilNormalizationScheme H hH I e :=
    closedGaussNormalizationSchemeChartInclusion H hH I e a
  j q

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- A prime of the original canonical normalized ratio ring has that
same prime localization as its actual global normalization scheme stalk. -/
noncomputable def closedGaussNormalizationSchemeChartStalkIso
    (a : Fin 4) (q : PrimeSpectrum (normalizationRing (Rₐ a))) :
    (closedGaussPencilNormalizationScheme H hH I e).presheaf.stalk
      (closedGaussNormalizationSchemeChartPoint H hH I e a q) ≃+* Localization.AtPrime q.asIdeal := by
  let j : Spec (CommRingCat.of (normalizationRing (Rₐ a))) ⟶
      closedGaussPencilNormalizationScheme H hH I e :=
    closedGaussNormalizationSchemeChartInclusion H hH I e a
  let : IsOpenImmersion j :=
    closedGaussNormalizationSchemeChartInclusion_isOpenImmersion H hH I e a
  unfold closedGaussNormalizationSchemeChartPoint
  exact schemeAffineOpenImmersionStalkIso (CommRingCat.of (normalizationRing (Rₐ a))) j q

end DimensionFourDependence
