import DimensionFourDependence.CategoricalPencilBaseField
import DimensionFourDependence.ClosedGaussParameterCurveScheme
import DimensionFourDependence.SchemeParameterSpread

/-! # The actual spread-out family of a normalized-pencil prime curve

The parameter model may be any scheme receiving the specified
extension-field point over the original constants. An actual normalized
affine curve supplies such a model. The source-parameter product and
the reduced integral closure of each prime curve are constructed.
-/

namespace DimensionFourDependence

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- A parameter model with the specified extension-field point and
the original constant-field action. The spread-out construction works
for any such model, including a smooth projective parameter curve. -/
structure ClosedGaussParameterSchemeModel
    {K : Type u} [Field K] [CharZero K]
    (H : Fin 4 → MvPolynomial (Fin 4) K) (I : ImageRelationWitness H)
    (E : Type u) [Field E] [Algebra (closedGaussParameterField H I) E] where
  curve : Scheme.{u}
  toBase : curve ⟶ Spec (CommRingCat.of K)
  generic : Spec (CommRingCat.of E) ⟶ curve
  generic_over : generic ≫ toBase =
    Spec.map (CommRingCat.ofHom (extendedClosedGaussSourceCoefficientHom H I E))

/-- The normalized affine parameter curve constructed from the actual
finite field extension supplies a concrete parameter model. -/
noncomputable def actualClosedGaussParameterSchemeModel
    {K : Type u} [Field K] [CharZero K]
    (H : Fin 4 → MvPolynomial (Fin 4) K) (I : ImageRelationWitness H)
    (E : Type u) [Field E] [Algebra (closedGaussParameterField H I) E]
    (e : RatFunc K ≃ₐ[K] closedGaussParameterField H I) :
    ClosedGaussParameterSchemeModel H I E where
  curve := closedGaussCoverParameterScheme H I E e
  toBase := closedGaussCoverParameterSchemeToBase H I E e
  generic := closedGaussCoverParameterGenericMorphism H I E e
  generic_over := closedGaussCoverParameterGenericMorphism_over H I E e

variable {K : Type u} [Field K] [CharZero K]
  (H : Fin 4 → MvPolynomial (Fin 4) K) (I : ImageRelationWitness H)
  (E : Type u) [Field E] [Algebra (closedGaussParameterField H I) E]
  [Algebra.IsAlgebraic (closedGaussParameterField H I) E]
  {d : ℕ} (hH : IsHomogMap H d)
  (e : RatFunc K ≃ₐ[K] closedGaussParameterField H I)
  (model : ClosedGaussParameterSchemeModel H I E)

local notation "Pₖ" => AlgebraicGeometry.Proj (homogeneousSubmodule (Fin 4) K)
local notation "Mₑ" => closedGaussPencilCoefficientBaseChangeNormalization H I E hH e
local notation "Cₑ" => ClosedGaussParameterSchemeModel.curve model
local notation "cₑ" => ClosedGaussParameterSchemeModel.toBase model
local notation "ηₑ" => ClosedGaussParameterSchemeModel.generic model
local notation "mₑ" => closedGaussPencilCoefficientBaseChangeNormalizationSourceMorphism H I E hH e
local notation "rₑ" => closedGaussPencilCoefficientBaseChangeNormalizationToBase H I E hH e

/-- The actual normalized pencil and actual parameter-curve generic
morphism have compatible original constant-field actions. -/
theorem closedGaussPencilSpreadSquare :
    (mₑ) ≫ polynomialProjectiveToBase K = (rₑ) ≫ (ηₑ) ≫ (cₑ) := by
  rw [model.generic_over]
  exact closedGaussPencilCoefficientBaseChangeNormalizationSourceMorphism_over_base_field H I E hH e

/-- The actual original-source and normalized-parameter-curve product. -/
noncomputable def closedGaussPencilSpreadAmbient : Scheme.{u} :=
  parameterSpreadAmbient (polynomialProjectiveToBase K) (cₑ)

/-- The actual normalized generic pencil maps into that product by its
original source and coefficient-field parameter morphisms. -/
noncomputable def closedGaussPencilSpreadMorphism :
    Mₑ ⟶ closedGaussPencilSpreadAmbient H I E model :=
  parameterSpreadMorphism (B := Spec (CommRingCat.of K)) (X := Pₖ) (Y := Mₑ)
    (T := Spec (CommRingCat.of E)) (C := Cₑ)
    (polynomialProjectiveToBase K) (cₑ) (mₑ) (rₑ) (ηₑ)
    (closedGaussPencilSpreadSquare H I E hH e model)

/-- The product map preserves the entire actual original source map. -/
theorem closedGaussPencilSpreadMorphism_fst :
    closedGaussPencilSpreadMorphism H I E hH e model ≫
      pullback.fst (polynomialProjectiveToBase K) (cₑ) = (mₑ) :=
  parameterSpreadMorphism_fst (polynomialProjectiveToBase K) (cₑ) (mₑ) (rₑ) (ηₑ)
    (closedGaussPencilSpreadSquare H I E hH e model)

/-- The actual reduced integral spread-out family of a prime
subvariety of the normalized generic pencil. -/
noncomputable def closedGaussPencilSpreadFamilyScheme (Z : Set Mₑ) (hZ : IsIrreducible Z) : Scheme.{u} :=
  parameterSpreadCurveFamilyScheme (B := Spec (CommRingCat.of K)) (X := Pₖ) (Y := Mₑ)
    (T := Spec (CommRingCat.of E)) (C := Cₑ)
    (polynomialProjectiveToBase K) (cₑ) (mₑ) (rₑ) (ηₑ)
    (closedGaussPencilSpreadSquare H I E hH e model) Z hZ

/-- The spread-out family's actual source projection. -/
noncomputable def closedGaussPencilSpreadFamilySourceMorphism (Z : Set Mₑ) (hZ : IsIrreducible Z) :
    closedGaussPencilSpreadFamilyScheme H I E hH e model Z hZ ⟶ Pₖ :=
  parameterSpreadCurveFamilySourceMorphism (B := Spec (CommRingCat.of K)) (X := Pₖ) (Y := Mₑ)
    (T := Spec (CommRingCat.of E)) (C := Cₑ)
    (polynomialProjectiveToBase K) (cₑ) (mₑ) (rₑ) (ηₑ)
    (closedGaussPencilSpreadSquare H I E hH e model) Z hZ

/-- The actual spread-out family is integral. -/
theorem closedGaussPencilSpreadFamilyScheme_isIntegral (Z : Set Mₑ) (hZ : IsIrreducible Z) :
    IsIntegral (closedGaussPencilSpreadFamilyScheme H I E hH e model Z hZ) :=
  parameterSpreadCurveFamilyScheme_isIntegral (B := Spec (CommRingCat.of K)) (X := Pₖ) (Y := Mₑ)
    (T := Spec (CommRingCat.of E)) (C := Cₑ)
    (polynomialProjectiveToBase K) (cₑ) (mₑ) (rₑ) (ηₑ)
    (closedGaussPencilSpreadSquare H I E hH e model) Z hZ

/-- Closing a prime curve over the actual normalized parameter model
does not change its closed original source image. -/
theorem closedGaussPencilSpreadFamilySourceMorphism_image_closure
    (Z : Set Mₑ) (hZ : IsIrreducible Z) (hZclosed : IsClosed Z) :
    closure (Set.range (closedGaussPencilSpreadFamilySourceMorphism H I E hH e model Z hZ)) =
      closure ((mₑ) '' Z) :=
  parameterSpreadCurveFamilySourceMorphism_image_closure
    (B := Spec (CommRingCat.of K)) (X := Pₖ) (Y := Mₑ)
    (T := Spec (CommRingCat.of E)) (C := Cₑ)
    (polynomialProjectiveToBase K) (cₑ) (mₑ) (rₑ) (ηₑ)
    (closedGaussPencilSpreadSquare H I E hH e model) Z hZ hZclosed

end DimensionFourDependence
