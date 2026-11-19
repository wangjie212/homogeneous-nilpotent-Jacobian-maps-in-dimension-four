import DimensionFourDependence.ClosedGaussPencilNormalizationScheme
import DimensionFourDependence.FiniteIntegralSchemeNormalization
import DimensionFourDependence.IntegralSchemeNormalizationNormal

/-! # The actual global pencil normalization is finite and proper

The original closed Gauss field has characteristic zero. Properness of
the actual pencil gives finite type over that field, so the global
normalization morphism is finite. Its composite to the original field
is proper and its source is Noetherian.
-/

namespace DimensionFourDependence

open AlgebraicGeometry CategoryTheory

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

variable {K : Type*} [Field K] [CharZero K]
  (H : Fin 4 → MvPolynomial (Fin 4) K) {d : ℕ} (hH : IsHomogMap H d)
  (I : ImageRelationWitness H) (e : RatFunc K ≃ₐ[K] closedGaussParameterField H I)

/-- The actual global normalization morphism of the original pencil is finite. -/
theorem closedGaussPencilNormalizationSchemeMap_isFinite :
    IsFinite (closedGaussPencilNormalizationSchemeMap H hH I e) := by
  let : CharZero (closedGaussParameterField H I) :=
    charZero_of_injective_algebraMap (algebraMap K (closedGaussParameterField H I)).injective
  let : IsIntegral (closedGaussPencilScheme H hH I e) := closedGaussPencilScheme_isIntegral H hH I e
  let : IsProper (closedGaussPencilSchemeToBase H hH I e) :=
    closedGaussPencilSchemeToBase_isProper H hH I e
  exact integralSchemeNormalizationMap_finite_of_finiteType
    (closedGaussPencilScheme H hH I e) (closedGaussPencilSchemeToBase H hH I e)

/-- The normalized projective pencil over its actual closed Gauss coefficient field. -/
noncomputable def closedGaussPencilNormalizationSchemeToBase :
    closedGaussPencilNormalizationScheme H hH I e ⟶
      Spec (CommRingCat.of (closedGaussParameterField H I)) :=
  closedGaussPencilNormalizationSchemeMap H hH I e ≫ closedGaussPencilSchemeToBase H hH I e

/-- The actual normalized pencil is proper over the original closed Gauss field. -/
theorem closedGaussPencilNormalizationSchemeToBase_isProper :
    IsProper (closedGaussPencilNormalizationSchemeToBase H hH I e) := by
  let : IsFinite (closedGaussPencilNormalizationSchemeMap H hH I e) :=
    closedGaussPencilNormalizationSchemeMap_isFinite H hH I e
  let : IsProper (closedGaussPencilSchemeToBase H hH I e) :=
    closedGaussPencilSchemeToBase_isProper H hH I e
  unfold closedGaussPencilNormalizationSchemeToBase
  infer_instance

/-- The actual normalized pencil is a Noetherian scheme. -/
theorem closedGaussPencilNormalizationScheme_isNoetherian :
    IsNoetherian (closedGaussPencilNormalizationScheme H hH I e) := by
  let : IsProper (closedGaussPencilNormalizationSchemeToBase H hH I e) :=
    closedGaussPencilNormalizationSchemeToBase_isProper H hH I e
  let : IsLocallyNoetherian (closedGaussPencilNormalizationScheme H hH I e) :=
    LocallyOfFiniteType.isLocallyNoetherian (closedGaussPencilNormalizationSchemeToBase H hH I e)
  let : CompactSpace (closedGaussPencilNormalizationScheme H hH I e) :=
    QuasiCompact.compactSpace_of_compactSpace (closedGaussPencilNormalizationSchemeToBase H hH I e)
  exact ⟨⟩

/-- Every local ring on the actual global normalized pencil is integrally closed. -/
theorem closedGaussPencilNormalizationScheme_stalk_isIntegrallyClosed
    (y : closedGaussPencilNormalizationScheme H hH I e) :
    IsIntegrallyClosed ((closedGaussPencilNormalizationScheme H hH I e).presheaf.stalk y) := by
  let : IsIntegral (closedGaussPencilScheme H hH I e) := closedGaussPencilScheme_isIntegral H hH I e
  exact integralSchemeNormalization_stalk_isIntegrallyClosed _ y

end DimensionFourDependence
