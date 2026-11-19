import DimensionFourDependence.ClosedGaussPencilScheme
import DimensionFourDependence.IntegralSchemeNormalization
import DimensionFourDependence.PolynomialProjectiveBase

/-! # Actual global pencil normalization and its projective base morphism

The projective pencil is proper over the original closed Gauss field.
Its function field constructs the global normalization scheme and its
integral morphism. The affine integral-closure gluing is actual scheme
data, rather than a hypothesized global object.
-/

namespace DimensionFourDependence

open AlgebraicGeometry CategoryTheory

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

variable {K : Type*} [Field K] [CharZero K]
  (H : Fin 4 → MvPolynomial (Fin 4) K) {d : ℕ} (hH : IsHomogMap H d)
  (I : ImageRelationWitness H) (e : RatFunc K ≃ₐ[K] closedGaussParameterField H I)

/-- The actual projective pencil over its original closed Gauss coefficient field. -/
noncomputable def closedGaussPencilSchemeToBase :
    closedGaussPencilScheme H hH I e ⟶ Spec (CommRingCat.of (closedGaussParameterField H I)) :=
  closedGaussPencilSchemeInclusion H hH I e ≫
    polynomialProjectiveToBase (closedGaussParameterField H I)

/-- Properness is derived for the actual original pencil and coefficient base. -/
theorem closedGaussPencilSchemeToBase_isProper :
    IsProper (closedGaussPencilSchemeToBase H hH I e) := by
  let : IsClosedImmersion (closedGaussPencilSchemeInclusion H hH I e) :=
    closedGaussPencilSchemeInclusion_isClosedImmersion H hH I e
  let : IsProper (polynomialProjectiveToBase (closedGaussParameterField H I)) :=
    polynomialProjectiveToBase_isProper _
  unfold closedGaussPencilSchemeToBase
  infer_instance

/-- The actual global normalization scheme of the projective pencil
in its own original function field. -/
noncomputable def closedGaussPencilNormalizationScheme : Scheme :=
  letI : IsIntegral (closedGaussPencilScheme H hH I e) := closedGaussPencilScheme_isIntegral H hH I e
  integralSchemeNormalization (closedGaussPencilScheme H hH I e)

/-- The actual integral normalization morphism back to the original pencil. -/
noncomputable def closedGaussPencilNormalizationSchemeMap :
    closedGaussPencilNormalizationScheme H hH I e ⟶ closedGaussPencilScheme H hH I e := by
  let : IsIntegral (closedGaussPencilScheme H hH I e) := closedGaussPencilScheme_isIntegral H hH I e
  exact integralSchemeNormalizationMap _

/-- The global pencil normalization is integral. -/
theorem closedGaussPencilNormalizationScheme_isIntegral :
    IsIntegral (closedGaussPencilNormalizationScheme H hH I e) := by
  let : IsIntegral (closedGaussPencilScheme H hH I e) := closedGaussPencilScheme_isIntegral H hH I e
  exact integralSchemeNormalization_isIntegral _

/-- Its original-pencil morphism is integral. Finiteness is a further
property, not included in the definition. -/
theorem closedGaussPencilNormalizationSchemeMap_isIntegralHom :
    IsIntegralHom (closedGaussPencilNormalizationSchemeMap H hH I e) := by
  let : IsIntegral (closedGaussPencilScheme H hH I e) := closedGaussPencilScheme_isIntegral H hH I e
  exact integralSchemeNormalizationMap_isIntegralHom _

/-- The actual function-field point factors through the constructed
global normalization and the original pencil. -/
theorem closedGaussPencilNormalizationScheme_function_field_factorization :
    letI : IsIntegral (closedGaussPencilScheme H hH I e) := closedGaussPencilScheme_isIntegral H hH I e
    ∃ j : Spec (closedGaussPencilScheme H hH I e).functionField ⟶
        closedGaussPencilNormalizationScheme H hH I e,
      j ≫ closedGaussPencilNormalizationSchemeMap H hH I e =
        integralSchemeGenericPointMorphism (closedGaussPencilScheme H hH I e) := by
  let : IsIntegral (closedGaussPencilScheme H hH I e) := closedGaussPencilScheme_isIntegral H hH I e
  exact ⟨integralSchemeNormalizationGenericPoint _, integralSchemeNormalization_factorization _⟩

end DimensionFourDependence
