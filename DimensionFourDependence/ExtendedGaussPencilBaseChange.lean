import DimensionFourDependence.ExtendedGaussPencilCartesianCharts
import DimensionFourDependence.ClosedGaussPencilOriginalAtlas

/-! # The actual extended pencil is the categorical coefficient base change

The checked tensor squares on the actual original affine cover prove
the global Cartesian property. The previously constructed comparison
is therefore an actual isomorphism, preserving both structure maps.
-/

namespace DimensionFourDependence

open MvPolynomial AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

universe u

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

variable {K : Type u} [Field K] [CharZero K]
  (H : Fin 4 → MvPolynomial (Fin 4) K) (I : ImageRelationWitness H)
  (E : Type u) [Field E] [Algebra (closedGaussParameterField H I) E]
  [Algebra.IsAlgebraic (closedGaussParameterField H I) E]
  {d : ℕ} (hH : IsHomogMap H d)
  (e : RatFunc K ≃ₐ[K] closedGaussParameterField H I)

local notation "C₀" => closedGaussParameterField H I
local notation "Q₀" => closedGaussPencilScheme H hH I e
local notation "Qₑ" => extendedClosedGaussPencilScheme H I E hH e
local notation "m" => extendedClosedGaussPencilToOriginal H I E hH e
local notation "p₀" => closedGaussPencilSchemeToBase H hH I e
local notation "pₑ" => extendedClosedGaussPencilSchemeToBase H I E hH e
local notation "c" => Spec.map (CommRingCat.ofHom (algebraMap C₀ E))

/-- The entire actual extended projective pencil, with its actual
original-pencil and coefficient maps, is a categorical coefficient base change. -/
theorem extendedClosedGaussPencil_coefficient_isPullback :
    IsPullback (m) (pₑ) (p₀) (c) := by
  let 𝒰 := (closedGaussPencilOriginalAffineCover H hH I e).openCover
  let A (a : Fin 4) := projectiveCoordinateChartAlgebra (C := C₀)
    (rationalCoordinate (K := K) (n := 4)) ((finSuccEquiv' a).symm none)
  let V (a : 𝒰.I₀) : Scheme.{u} := Spec (CommRingCat.of (A a ⊗[C₀] E))
  let j (a : 𝒰.I₀) : V a ⟶ Qₑ :=
    extendedClosedGaussPencilTensorChartInclusion H I E hH e (finSuccEquiv' a)
  let r (a : 𝒰.I₀) : V a ⟶ 𝒰.X a :=
    Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeft : A a →ₐ[C₀] A a ⊗[C₀] E).toRingHom)
  apply scheme_isPullback_of_chart_squares
    (W := Qₑ) (X := Q₀) (Y := Spec (CommRingCat.of E)) (Z := Spec (CommRingCat.of C₀))
    (m) (pₑ) (p₀) (c) 𝒰 V j r
  · intro a
    change IsPullback (extendedClosedGaussPencilTensorChartInclusion H I E hH e (finSuccEquiv' a))
      (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeft : A a →ₐ[C₀] A a ⊗[C₀] E).toRingHom))
      (m) (closedGaussPencilChartInclusion H I hH e (finSuccEquiv' a))
    exact extendedClosedGaussPencilTensorChart_original_isPullback H I E hH e (finSuccEquiv' a)
  · intro a
    change IsPullback
      (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeft : A a →ₐ[C₀] A a ⊗[C₀] E).toRingHom))
      (extendedClosedGaussPencilTensorChartInclusion H I E hH e (finSuccEquiv' a) ≫ (pₑ))
      (closedGaussPencilChartInclusion H I hH e (finSuccEquiv' a) ≫ (p₀)) (c)
    exact extendedClosedGaussPencilTensorChart_coefficient_isPullback H I E hH e (finSuccEquiv' a)

/-- The canonical comparison with the categorical coefficient base
change is an isomorphism, proved from its actual affine tensor charts. -/
theorem extendedClosedGaussPencilBaseChangeComparison_isIso :
    IsIso (extendedClosedGaussPencilBaseChangeComparison H I E hH e) := by
  have h := extendedClosedGaussPencil_coefficient_isPullback H I E hH e
  have hm : extendedClosedGaussPencilBaseChangeComparison H I E hH e = h.isoPullback.hom := by
    apply pullback.hom_ext
    · exact (extendedClosedGaussPencilBaseChangeComparison_fst H I E hH e).trans h.isoPullback_hom_fst.symm
    · exact (extendedClosedGaussPencilBaseChangeComparison_snd H I E hH e).trans h.isoPullback_hom_snd.symm
  rw [hm]
  exact h.isoPullback.isIso_hom

/-- The actual coefficient-extended projective pencil identified
with the categorical base change of the original projective pencil. -/
noncomputable def extendedClosedGaussPencilCoefficientBaseChangeIso :
    Qₑ ≅ closedGaussPencilCoefficientBaseChange H I E hH e := by
  let : IsIso (extendedClosedGaussPencilBaseChangeComparison H I E hH e) :=
    extendedClosedGaussPencilBaseChangeComparison_isIso H I E hH e
  exact asIso (extendedClosedGaussPencilBaseChangeComparison H I E hH e)

/-- The base-change isomorphism preserves the actual original-pencil projection. -/
theorem extendedClosedGaussPencilCoefficientBaseChangeIso_fst :
    (extendedClosedGaussPencilCoefficientBaseChangeIso H I E hH e).hom ≫ pullback.fst _ _ = (m) := by
  exact extendedClosedGaussPencilBaseChangeComparison_fst H I E hH e

/-- The base-change isomorphism preserves the actual extended-field structure map. -/
theorem extendedClosedGaussPencilCoefficientBaseChangeIso_snd :
    (extendedClosedGaussPencilCoefficientBaseChangeIso H I E hH e).hom ≫ pullback.snd _ _ = (pₑ) := by
  exact extendedClosedGaussPencilBaseChangeComparison_snd H I E hH e

end DimensionFourDependence
