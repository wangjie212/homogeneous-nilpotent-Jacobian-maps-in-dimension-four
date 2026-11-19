import DimensionFourDependence.ExtendedGaussPencilOriginalMap
import DimensionFourDependence.ClosedGaussPencilNormalizationScheme
import DimensionFourDependence.ProjectiveCoefficientBaseMap
import Mathlib.AlgebraicGeometry.Pullbacks

/-! # The actual morphism to the categorical coefficient base change -/

namespace DimensionFourDependence

open MvPolynomial AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {K : Type u} [Field K] [CharZero K]
  (H : Fin 4 → MvPolynomial (Fin 4) K) (I : ImageRelationWitness H)
  (E : Type u) [Field E] [Algebra (closedGaussParameterField H I) E]
  [Algebra.IsAlgebraic (closedGaussParameterField H I) E]
  {d : ℕ} (hH : IsHomogMap H d)
  (e : RatFunc K ≃ₐ[K] closedGaussParameterField H I)

local notation "C₀" => closedGaussParameterField H I

/-- The actual morphism to the original pencil commutes with both
specified coefficient-field structure morphisms. -/
theorem extendedClosedGaussPencilToOriginal_over :
    extendedClosedGaussPencilToOriginal H I E hH e ≫ closedGaussPencilSchemeToBase H hH I e =
      extendedClosedGaussPencilSchemeToBase H I E hH e ≫ Spec.map (CommRingCat.ofHom (algebraMap C₀ E)) := by
  unfold closedGaussPencilSchemeToBase extendedClosedGaussPencilSchemeToBase
  rw [← Category.assoc, extendedClosedGaussPencilToOriginal_inclusion,
    Category.assoc, polynomialProjectiveCoefficientMap_to_base, Category.assoc]

/-- The categorical base change of the original projective Gauss pencil
along the given coefficient-field extension. -/
noncomputable def closedGaussPencilCoefficientBaseChange : Scheme.{u} :=
  pullback (closedGaussPencilSchemeToBase H hH I e) (Spec.map (CommRingCat.ofHom (algebraMap C₀ E)))

/-- The constructed extended pencil has its actual canonical map to
the categorical coefficient base change. Its being an isomorphism is a
further property, not built into this definition. -/
noncomputable def extendedClosedGaussPencilBaseChangeComparison :
    extendedClosedGaussPencilScheme H I E hH e ⟶ closedGaussPencilCoefficientBaseChange H I E hH e :=
  pullback.lift (extendedClosedGaussPencilToOriginal H I E hH e)
    (extendedClosedGaussPencilSchemeToBase H I E hH e) (extendedClosedGaussPencilToOriginal_over H I E hH e)

/-- The comparison retains the actual original-pencil morphism. -/
theorem extendedClosedGaussPencilBaseChangeComparison_fst :
    extendedClosedGaussPencilBaseChangeComparison H I E hH e ≫ pullback.fst _ _ =
      extendedClosedGaussPencilToOriginal H I E hH e := pullback.lift_fst _ _ _

/-- The comparison retains the actual extended coefficient structure map. -/
theorem extendedClosedGaussPencilBaseChangeComparison_snd :
    extendedClosedGaussPencilBaseChangeComparison H I E hH e ≫ pullback.snd _ _ =
      extendedClosedGaussPencilSchemeToBase H I E hH e := pullback.lift_snd _ _ _

end DimensionFourDependence
