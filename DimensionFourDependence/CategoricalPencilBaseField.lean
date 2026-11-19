import DimensionFourDependence.ClosedGaussPencilBaseChangeNormalization
import DimensionFourDependence.ProjectiveCoefficientBaseMap

/-! # The categorical normalized pencil retains the original base field -/

namespace DimensionFourDependence

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial

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

local notation "C₀" => closedGaussParameterField H I
local notation "Bₑ" => closedGaussPencilCoefficientBaseChange H I E hH e
local notation "Mₑ" => closedGaussPencilCoefficientBaseChangeNormalization H I E hH e

/-- The original pencil source projection preserves its original
coefficient-field structure morphism. -/
theorem closedGaussPencilSourceMorphism_over_base_field :
    closedGaussPencilSourceMorphism H I hH e ≫ polynomialProjectiveToBase K =
      closedGaussPencilSchemeToBase H hH I e ≫
        Spec.map (CommRingCat.ofHom (algebraMap K C₀)) := by
  unfold closedGaussPencilSourceMorphism closedGaussPencilSchemeToBase
  rw [Category.assoc, polynomialProjectiveCoefficientMap_to_base, Category.assoc]

/-- The actual categorical coefficient projection. -/
noncomputable def closedGaussPencilCoefficientBaseChangeToBase : Bₑ ⟶ Spec (CommRingCat.of E) :=
  pullback.snd _ _

/-- The source and coefficient projections agree on the entire original
base field, with the specified original coefficient homomorphism. -/
theorem closedGaussPencilCoefficientBaseChangeSourceMorphism_over_base_field :
    closedGaussPencilCoefficientBaseChangeSourceMorphism H I E hH e ≫ polynomialProjectiveToBase K =
      closedGaussPencilCoefficientBaseChangeToBase H I E hH e ≫
        Spec.map (CommRingCat.ofHom (extendedClosedGaussSourceCoefficientHom H I E)) := by
  unfold closedGaussPencilCoefficientBaseChangeSourceMorphism
    closedGaussPencilCoefficientBaseChangeToBase
  rw [Category.assoc, closedGaussPencilSourceMorphism_over_base_field,
    ← Category.assoc, pullback.condition, Category.assoc, ← Spec.map_comp]
  rfl

/-- The intrinsic categorical normalization's structure morphism to
the actual coefficient extension field. -/
noncomputable def closedGaussPencilCoefficientBaseChangeNormalizationToBase :
    Mₑ ⟶ Spec (CommRingCat.of E) :=
  closedGaussPencilCoefficientBaseChangeNormalizationMap H I E hH e ≫
    closedGaussPencilCoefficientBaseChangeToBase H I E hH e

/-- The actual normalized source projection is a morphism over the
original field through its specified extended coefficient structure. -/
theorem closedGaussPencilCoefficientBaseChangeNormalizationSourceMorphism_over_base_field :
    closedGaussPencilCoefficientBaseChangeNormalizationSourceMorphism H I E hH e ≫
        polynomialProjectiveToBase K =
      closedGaussPencilCoefficientBaseChangeNormalizationToBase H I E hH e ≫
        Spec.map (CommRingCat.ofHom (extendedClosedGaussSourceCoefficientHom H I E)) := by
  unfold closedGaussPencilCoefficientBaseChangeNormalizationSourceMorphism
    closedGaussPencilCoefficientBaseChangeNormalizationToBase
  rw [Category.assoc, closedGaussPencilCoefficientBaseChangeSourceMorphism_over_base_field,
    Category.assoc]

/-- The intrinsic categorical normalization is proper over its actual
coefficient extension field, using the actual categorical projection. -/
theorem closedGaussPencilCoefficientBaseChangeNormalizationToBase_isProper :
    IsProper (closedGaussPencilCoefficientBaseChangeNormalizationToBase H I E hH e) := by
  let : IsProper (closedGaussPencilSchemeToBase H hH I e) :=
    closedGaussPencilSchemeToBase_isProper H hH I e
  let : IsProper (closedGaussPencilCoefficientBaseChangeToBase H I E hH e) :=
    inferInstanceAs (IsProper (pullback.snd (closedGaussPencilSchemeToBase H hH I e)
      (Spec.map (CommRingCat.ofHom (algebraMap C₀ E)))))
  let : IsFinite (closedGaussPencilCoefficientBaseChangeNormalizationMap H I E hH e) :=
    closedGaussPencilCoefficientBaseChangeNormalizationMap_isFinite H I E hH e
  unfold closedGaussPencilCoefficientBaseChangeNormalizationToBase
  infer_instance

end DimensionFourDependence
