import DimensionFourDependence.ExtendedGaussPencilBaseChange
import DimensionFourDependence.ProjectiveCoefficientComposition

/-! # The categorical pencil base change retains the original projective source -/

namespace DimensionFourDependence

open MvPolynomial AlgebraicGeometry CategoryTheory CategoryTheory.Limits

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

local notation "C₀" => closedGaussParameterField H I
local notation "Pₖ" => AlgebraicGeometry.Proj (homogeneousSubmodule (Fin 4) K)

/-- The original projective pencil maps to the original projective
source through its original homogeneous coordinates. -/
noncomputable def closedGaussPencilSourceMorphism : closedGaussPencilScheme H hH I e ⟶ Pₖ :=
  closedGaussPencilSchemeInclusion H hH I e ≫ polynomialProjectiveCoefficientMap (algebraMap K C₀)

/-- The source projection on the categorical coefficient base change. -/
noncomputable def closedGaussPencilCoefficientBaseChangeSourceMorphism :
    closedGaussPencilCoefficientBaseChange H I E hH e ⟶ Pₖ :=
  pullback.fst _ _ ≫ closedGaussPencilSourceMorphism H I hH e

/-- The constructed morphism to the original pencil retains the
entire actual projection to the original projective source. -/
theorem extendedClosedGaussPencilToOriginal_source :
    extendedClosedGaussPencilToOriginal H I E hH e ≫ closedGaussPencilSourceMorphism H I hH e =
      extendedClosedGaussPencilSourceMorphism H I E hH e := by
  unfold closedGaussPencilSourceMorphism extendedClosedGaussPencilSourceMorphism
  rw [← Category.assoc, extendedClosedGaussPencilToOriginal_inclusion,
    Category.assoc, ← polynomialProjectiveCoefficientMap_comp]
  rfl

/-- The global base-change isomorphism preserves the actual source
projection used in every checked divisor-order theorem. -/
theorem extendedClosedGaussPencilCoefficientBaseChangeIso_source :
    (extendedClosedGaussPencilCoefficientBaseChangeIso H I E hH e).hom ≫
        closedGaussPencilCoefficientBaseChangeSourceMorphism H I E hH e =
      extendedClosedGaussPencilSourceMorphism H I E hH e := by
  unfold closedGaussPencilCoefficientBaseChangeSourceMorphism
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun k => k ≫ closedGaussPencilSourceMorphism H I hH e)
      (extendedClosedGaussPencilCoefficientBaseChangeIso_fst H I E hH e)).trans
        (extendedClosedGaussPencilToOriginal_source H I E hH e))

/-- The actual normalized pencil's finite map to the categorical
coefficient base change, through the checked extended-pencil isomorphism. -/
noncomputable def extendedClosedGaussNormalizationToCoefficientBaseChange :
    extendedClosedGaussNormalizationScheme H I E hH e ⟶ closedGaussPencilCoefficientBaseChange H I E hH e :=
  extendedClosedGaussNormalizationSchemeMap H I E hH e ≫
    (extendedClosedGaussPencilCoefficientBaseChangeIso H I E hH e).hom

/-- This actual morphism to the categorical base change is finite. -/
theorem extendedClosedGaussNormalizationToCoefficientBaseChange_isFinite :
    IsFinite (extendedClosedGaussNormalizationToCoefficientBaseChange H I E hH e) := by
  let : IsFinite (extendedClosedGaussNormalizationSchemeMap H I E hH e) :=
    extendedClosedGaussNormalizationSchemeMap_isFinite H I E hH e
  unfold extendedClosedGaussNormalizationToCoefficientBaseChange
  infer_instance

/-- The normalized map to the categorical base change retains the
same entire original source morphism, rather than only its chart values. -/
theorem extendedClosedGaussNormalizationToCoefficientBaseChange_source :
    extendedClosedGaussNormalizationToCoefficientBaseChange H I E hH e ≫
        closedGaussPencilCoefficientBaseChangeSourceMorphism H I E hH e =
      extendedClosedGaussNormalizationSourceMorphism H I E hH e := by
  unfold extendedClosedGaussNormalizationToCoefficientBaseChange extendedClosedGaussNormalizationSourceMorphism
  rw [Category.assoc, extendedClosedGaussPencilCoefficientBaseChangeIso_source]

/-- The normalized map retains the actual original-pencil projection. -/
theorem extendedClosedGaussNormalizationToCoefficientBaseChange_fst :
    extendedClosedGaussNormalizationToCoefficientBaseChange H I E hH e ≫ pullback.fst _ _ =
      extendedClosedGaussNormalizationSchemeMap H I E hH e ≫
        extendedClosedGaussPencilToOriginal H I E hH e := by
  unfold extendedClosedGaussNormalizationToCoefficientBaseChange
  exact (Category.assoc _ _ _).trans
    (congrArg (fun k => extendedClosedGaussNormalizationSchemeMap H I E hH e ≫ k)
      (extendedClosedGaussPencilCoefficientBaseChangeIso_fst H I E hH e))

/-- The normalized map retains the actual extended coefficient structure map. -/
theorem extendedClosedGaussNormalizationToCoefficientBaseChange_snd :
    extendedClosedGaussNormalizationToCoefficientBaseChange H I E hH e ≫ pullback.snd _ _ =
      extendedClosedGaussNormalizationSchemeToBase H I E hH e := by
  unfold extendedClosedGaussNormalizationToCoefficientBaseChange extendedClosedGaussNormalizationSchemeToBase
  exact (Category.assoc _ _ _).trans
    (congrArg (fun k => extendedClosedGaussNormalizationSchemeMap H I E hH e ≫ k)
      (extendedClosedGaussPencilCoefficientBaseChangeIso_snd H I E hH e))

end DimensionFourDependence
