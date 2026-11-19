import DimensionFourDependence.ClosedGaussPencilSpreadScheme
import DimensionFourDependence.ExtendedNativeSourceFormPullbacks

/-! # Actual spread-out source families for prime subvarieties of the native pencil -/

namespace DimensionFourDependence

open AlgebraicGeometry CategoryTheory MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 2000000
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {K : Type u} [Field K] [CharZero K]
  (H : Fin 4 → MvPolynomial (Fin 4) K) (I : ImageRelationWitness H)
  (E : Type u) [Field E] [Algebra (closedGaussParameterField H I) E]
  [Algebra.IsAlgebraic (closedGaussParameterField H I) E]
  {d : ℕ} (hH : IsHomogMap H d)
  (e : RatFunc K ≃ₐ[K] closedGaussParameterField H I)

local notation "N" => extendedClosedGaussNormalizationScheme H I E hH e
local notation "m" => extendedClosedGaussNormalizationSourceMorphism H I E hH e
local notation "r" => extendedClosedGaussNormalizationSchemeToBase H I E hH e
local notation "P₀" => AlgebraicGeometry.Proj (homogeneousSubmodule (Fin 4) K)

/-- The actual native source and coefficient projections retain
the specified entire original constant-field structure. -/
theorem extendedClosedGaussNormalizationSourceMorphism_over_base_field :
    (m) ≫ polynomialProjectiveToBase K = (r) ≫
      Spec.map (CommRingCat.ofHom (extendedClosedGaussSourceCoefficientHom H I E)) := by
  unfold extendedClosedGaussNormalizationSourceMorphism extendedClosedGaussPencilSourceMorphism
    extendedClosedGaussNormalizationSchemeToBase extendedClosedGaussPencilSchemeToBase
  simp only [Category.assoc, polynomialProjectiveCoefficientMap_to_base]

variable (model : ClosedGaussParameterSchemeModel H I E)

local notation "C₀" => ClosedGaussParameterSchemeModel.curve model
local notation "c₀" => ClosedGaussParameterSchemeModel.toBase model
local notation "η₀" => ClosedGaussParameterSchemeModel.generic model

/-- The actual native pencil and the actual parameter model give
a compatible source-parameter product diagram over the original field. -/
theorem nativeClosedGaussPencilSpreadSquare :
    (m) ≫ polynomialProjectiveToBase K = (r) ≫ (η₀) ≫ (c₀) := by
  rw [model.generic_over]
  exact extendedClosedGaussNormalizationSourceMorphism_over_base_field H I E hH e

/-- The actual reduced integral family obtained by closing a native
prime subvariety in the original source-parameter product. -/
noncomputable def nativeClosedGaussPencilSpreadFamilyScheme (Z : Set N) (hZ : IsIrreducible Z) : Scheme.{u} :=
  parameterSpreadCurveFamilyScheme (B := Spec (CommRingCat.of K)) (X := P₀) (Y := N)
    (T := Spec (CommRingCat.of E)) (C := C₀)
    (polynomialProjectiveToBase K) (c₀) (m) (r) (η₀)
    (nativeClosedGaussPencilSpreadSquare H I E hH e model) Z hZ

/-- The entire actual source projection of the native spread-out family. -/
noncomputable def nativeClosedGaussPencilSpreadFamilySourceMorphism (Z : Set N) (hZ : IsIrreducible Z) :
    nativeClosedGaussPencilSpreadFamilyScheme H I E hH e model Z hZ ⟶ P₀ :=
  parameterSpreadCurveFamilySourceMorphism (B := Spec (CommRingCat.of K)) (X := P₀) (Y := N)
    (T := Spec (CommRingCat.of E)) (C := C₀)
    (polynomialProjectiveToBase K) (c₀) (m) (r) (η₀)
    (nativeClosedGaussPencilSpreadSquare H I E hH e model) Z hZ

/-- This is an actual integral scheme, without an assumed local
surface model for the spread-out prime subvariety. -/
theorem nativeClosedGaussPencilSpreadFamilyScheme_isIntegral (Z : Set N) (hZ : IsIrreducible Z) :
    IsIntegral (nativeClosedGaussPencilSpreadFamilyScheme H I E hH e model Z hZ) :=
  parameterSpreadCurveFamilyScheme_isIntegral (B := Spec (CommRingCat.of K)) (X := P₀) (Y := N)
    (T := Spec (CommRingCat.of E)) (C := C₀)
    (polynomialProjectiveToBase K) (c₀) (m) (r) (η₀)
    (nativeClosedGaussPencilSpreadSquare H I E hH e model) Z hZ

/-- The native spread-out family has exactly the original native
prime subvariety's closed source image, in the same original coordinates. -/
theorem nativeClosedGaussPencilSpreadFamilySourceMorphism_image_closure
    (Z : Set N) (hZ : IsIrreducible Z) (hZclosed : IsClosed Z) :
    closure (Set.range (nativeClosedGaussPencilSpreadFamilySourceMorphism H I E hH e model Z hZ)) =
      closure ((m) '' Z) :=
  parameterSpreadCurveFamilySourceMorphism_image_closure (B := Spec (CommRingCat.of K)) (X := P₀) (Y := N)
    (T := Spec (CommRingCat.of E)) (C := C₀)
    (polynomialProjectiveToBase K) (c₀) (m) (r) (η₀)
    (nativeClosedGaussPencilSpreadSquare H I E hH e model) Z hZ hZclosed

end DimensionFourDependence
