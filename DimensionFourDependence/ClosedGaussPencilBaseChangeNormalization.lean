import DimensionFourDependence.ClosedGaussPencilBaseChangeSource
import DimensionFourDependence.IntegralSchemeNormalizationIso
import DimensionFourDependence.IntegralSchemeNormalizationNormal

/-! # Intrinsic normalization of the categorical coefficient base change

The actual extended-pencil normalization is identified with the
normalization formed in the categorical pullback's own function field.
The isomorphism retains its normalization and original-source maps.
-/

namespace DimensionFourDependence

open AlgebraicGeometry CategoryTheory

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

local notation "Qₑ" => extendedClosedGaussPencilScheme H I E hH e
local notation "Bₑ" => closedGaussPencilCoefficientBaseChange H I E hH e
local notation "Nₑ" => extendedClosedGaussNormalizationScheme H I E hH e

/-- The actual categorical coefficient base change is integral,
through the checked actual extended-pencil isomorphism. -/
theorem closedGaussPencilCoefficientBaseChange_isIntegral : IsIntegral Bₑ := by
  let : IsIntegral Qₑ := extendedClosedGaussPencilScheme_isIntegral H I E hH e
  exact IsIntegral.of_isIso (extendedClosedGaussPencilCoefficientBaseChangeIso H I E hH e).hom

/-- Normalization formed in the categorical coefficient pullback's
own actual scheme function field. -/
noncomputable def closedGaussPencilCoefficientBaseChangeNormalization : Scheme.{u} :=
  letI : IsIntegral Bₑ := closedGaussPencilCoefficientBaseChange_isIntegral H I E hH e
  integralSchemeNormalization Bₑ

/-- The actual intrinsic normalization morphism to the categorical pullback. -/
noncomputable def closedGaussPencilCoefficientBaseChangeNormalizationMap :
    closedGaussPencilCoefficientBaseChangeNormalization H I E hH e ⟶ Bₑ := by
  let : IsIntegral Bₑ := closedGaussPencilCoefficientBaseChange_isIntegral H I E hH e
  exact integralSchemeNormalizationMap Bₑ

/-- Its actual morphism to the original projective source. -/
noncomputable def closedGaussPencilCoefficientBaseChangeNormalizationSourceMorphism :=
  closedGaussPencilCoefficientBaseChangeNormalizationMap H I E hH e ≫
    closedGaussPencilCoefficientBaseChangeSourceMorphism H I E hH e

/-- The constructed extended normalization is the intrinsic
normalization of the categorical coefficient base change. -/
noncomputable def extendedClosedGaussNormalizationCoefficientBaseChangeIso :
    Nₑ ≅ closedGaussPencilCoefficientBaseChangeNormalization H I E hH e := by
  let : IsIntegral Qₑ := extendedClosedGaussPencilScheme_isIntegral H I E hH e
  let : IsIntegral Bₑ := closedGaussPencilCoefficientBaseChange_isIntegral H I E hH e
  exact integralSchemeNormalizationIso (X := Qₑ) (Y := Bₑ)
    (extendedClosedGaussPencilCoefficientBaseChangeIso H I E hH e)

/-- The intrinsic normalization identification retains the actual
finite map to the categorical coefficient base change. -/
theorem extendedClosedGaussNormalizationCoefficientBaseChangeIso_map :
    (extendedClosedGaussNormalizationCoefficientBaseChangeIso H I E hH e).hom ≫
        closedGaussPencilCoefficientBaseChangeNormalizationMap H I E hH e =
      extendedClosedGaussNormalizationToCoefficientBaseChange H I E hH e := by
  let : IsIntegral Qₑ := extendedClosedGaussPencilScheme_isIntegral H I E hH e
  let : IsIntegral Bₑ := closedGaussPencilCoefficientBaseChange_isIntegral H I E hH e
  exact integralSchemeNormalizationIso_map (X := Qₑ) (Y := Bₑ)
    (extendedClosedGaussPencilCoefficientBaseChangeIso H I E hH e)

/-- The entire original source projection is preserved by the
intrinsic categorical normalization isomorphism. -/
theorem extendedClosedGaussNormalizationCoefficientBaseChangeIso_source :
    (extendedClosedGaussNormalizationCoefficientBaseChangeIso H I E hH e).hom ≫
        closedGaussPencilCoefficientBaseChangeNormalizationSourceMorphism H I E hH e =
      extendedClosedGaussNormalizationSourceMorphism H I E hH e := by
  unfold closedGaussPencilCoefficientBaseChangeNormalizationSourceMorphism
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun k => k ≫ closedGaussPencilCoefficientBaseChangeSourceMorphism H I E hH e)
      (extendedClosedGaussNormalizationCoefficientBaseChangeIso_map H I E hH e)).trans
        (extendedClosedGaussNormalizationToCoefficientBaseChange_source H I E hH e))

/-- The intrinsic categorical normalization map is finite. -/
theorem closedGaussPencilCoefficientBaseChangeNormalizationMap_isFinite :
    IsFinite (closedGaussPencilCoefficientBaseChangeNormalizationMap H I E hH e) := by
  let n := extendedClosedGaussNormalizationCoefficientBaseChangeIso H I E hH e
  let : IsIso n.hom := n.isIso_hom
  have h : IsFinite (n.hom ≫ closedGaussPencilCoefficientBaseChangeNormalizationMap H I E hH e) := by
    rw [extendedClosedGaussNormalizationCoefficientBaseChangeIso_map]
    exact extendedClosedGaussNormalizationToCoefficientBaseChange_isFinite H I E hH e
  exact (MorphismProperty.cancel_left_of_respectsIso @IsFinite n.hom
    (closedGaussPencilCoefficientBaseChangeNormalizationMap H I E hH e)).mp h

/-- The categorical normalization itself is integral. -/
theorem closedGaussPencilCoefficientBaseChangeNormalization_isIntegral :
    IsIntegral (closedGaussPencilCoefficientBaseChangeNormalization H I E hH e) := by
  let : IsIntegral Bₑ := closedGaussPencilCoefficientBaseChange_isIntegral H I E hH e
  exact integralSchemeNormalization_isIntegral Bₑ

/-- Every stalk on this intrinsic categorical normalization is integrally closed. -/
theorem closedGaussPencilCoefficientBaseChangeNormalization_stalk_isIntegrallyClosed
    (y : closedGaussPencilCoefficientBaseChangeNormalization H I E hH e) :
    IsIntegrallyClosed ((closedGaussPencilCoefficientBaseChangeNormalization H I E hH e).presheaf.stalk y) := by
  let : IsIntegral Bₑ := closedGaussPencilCoefficientBaseChange_isIntegral H I E hH e
  exact integralSchemeNormalization_stalk_isIntegrallyClosed Bₑ y

end DimensionFourDependence
