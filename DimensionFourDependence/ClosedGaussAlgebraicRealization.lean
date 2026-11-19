import DimensionFourDependence.CompatibleAlgebraicSourceRealization
import DimensionFourDependence.AffineSourceConeForm
import DimensionFourDependence.SourceTensorPolynomialValues
import DimensionFourDependence.NativeGraphNormalComparison

/-! # Actual algebraic Gauss coefficients and affine source retain one realization

The source and closed Gauss embeddings of a geometric component extend
to the actual algebraic coefficient field. Every coefficient, original
coordinate and original polynomial value is retained. The coefficient
images are algebraic over the same closed-field range in the constants.
-/

namespace DimensionFourDependence

open MvPolynomial
open scoped TensorProduct

attribute [local instance] Algebra.TensorProduct.rightAlgebra

set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

section Algebraicity

variable {K C L E : Type*} [Field K] [Field C] [Field L] [Field E]
    [Algebra K C] [Algebra K E] [Algebra C L] [Algebra.IsAlgebraic C L]

/-- Every image of the algebraic coefficient extension is algebraic
over the exact field range of the compatible closed coefficient image. -/
theorem compatible_algebraic_coefficient_image_isAlgebraic_over_fieldRange
    (g : C →ₐ[K] E) (σ : L →+* E)
    (hσ : ∀ c : C, σ (algebraMap C L c) = g c) (l : L) :
    IsAlgebraic g.fieldRange (σ l) := by
  have he : (algebraMap g.fieldRange E).comp g.equivFieldRange.toRingHom =
      σ.comp (algebraMap C L) := by
    ext c
    change g c = σ (algebraMap C L c)
    exact (hσ c).symm
  exact (Algebra.IsAlgebraic.isAlgebraic (R := C) l).ringHom_of_comp_eq
    g.equivFieldRange.toRingHom σ g.equivFieldRange.injective he

end Algebraicity

universe u

variable {K : Type u} [Field K] [CharZero K]
    (H : Fin 4 → MvPolynomial (Fin 4) K) (I : ImageRelationWitness H)
    (L : Type u) [Field L] [Algebra (closedGaussParameterField H I) L]
    [Algebra.IsAlgebraic (closedGaussParameterField H I) L]
    {E G : Type u} [Field E] [Field G] [Algebra K E] [Algebra E G] [Algebra K G]
    [IsScalarTower K E G] [IsAlgClosed E]

local notation "C₀" => closedGaussParameterField H I
local notation "S₀" => FractionRing (MvPolynomial (Fin 4) K)
local notation "T₀" => S₀ ⊗[C₀] L
local notation "F₀" => FractionRing T₀
local notation "xₐ" => extendedClosedGaussAffineTensorCoordinate H I L

local instance closedGaussAlgebraicRealizationDomain : IsDomain T₀ :=
  (actual_closed_gauss_cover_algebraic_base_change_isField H I L).isDomain

/-- A compatible actual source and closed Gauss realization extends
to all algebraic coefficients and the entire affine source fraction
field. The original polynomial values and coordinates remain exact. -/
theorem compatible_closed_gauss_realization_extends_to_affine_source
    (f : S₀ →ₐ[K] G) (g : C₀ →ₐ[K] E)
    (hg : ∀ c : C₀, algebraMap E G (g c) = f (c : S₀)) :
    ∃ σ : L →+* E, (∀ c : C₀, σ (algebraMap C₀ L c) = g c) ∧
      (∀ l : L, IsAlgebraic g.fieldRange (σ l)) ∧
      ∃ φ : F₀ →+* G,
        (∀ s : S₀, φ (algebraMap T₀ F₀ (s ⊗ₜ[C₀] (1 : L))) = f s) ∧
        (∀ l : L, φ (algebraMap L F₀ l) = algebraMap E G (σ l)) ∧
        (∀ i : Fin 4, φ ((xₐ) i) = f (rationalCoordinate (K := K) i)) ∧
        (∀ Q : MvPolynomial (Fin 4) K,
          φ (aeval (xₐ) (MvPolynomial.map (extendedClosedGaussSourceCoefficientHom H I L) Q)) =
            f (algebraMap (MvPolynomial (Fin 4) K) S₀ Q)) := by
  classical
  obtain ⟨σ, hσ, φ, hsource, hcoeff⟩ :=
    compatible_closed_field_realization_extends_to_algebraic_source_fraction_field
      (L := L) (closedGaussParameterField_relatively_closed H I) f g hg
  refine ⟨σ, hσ, compatible_algebraic_coefficient_image_isAlgebraic_over_fieldRange g σ hσ,
    φ, hsource, ?_, ?_, ?_⟩
  · intro l
    exact hcoeff l
  · intro i
    exact hsource (rationalCoordinate (K := K) i)
  · intro Q
    have he := comp_aeval_apply (extendedClosedGaussSourceTensorCoordinate H I L)
      (IsScalarTower.toAlgHom L T₀ F₀)
      (MvPolynomial.map (extendedClosedGaussSourceCoefficientHom H I L) Q)
    change algebraMap T₀ F₀
      (aeval (extendedClosedGaussSourceTensorCoordinate H I L)
        (MvPolynomial.map (extendedClosedGaussSourceCoefficientHom H I L) Q)) =
      aeval (xₐ) (MvPolynomial.map (extendedClosedGaussSourceCoefficientHom H I L) Q) at he
    rw [← he, extendedClosedGaussSourceTensorCoordinate_original_constant_polynomial_value, hsource]

omit [Algebra.IsAlgebraic (closedGaussParameterField H I) L] in
/-- The first ruling row realizes exactly the actual closed Gauss
normal under every compatible extended coefficient embedding. -/
theorem compatible_algebraic_coefficient_chosen_normal_value
    (g : C₀ →ₐ[K] E) (σ : L →+* E) (hσ : ∀ c : C₀, σ (algebraMap C₀ L c) = g c)
    {d : ℕ} (hH : IsHomogMap H d) (hd : 0 < d) (hind : ¬ ComponentsDependent H)
    (hGauss : gaussImageDimension H I = 1)
    (e : RatFunc K ≃ₐ[K] C₀) (i : Fin 4) :
    σ (extendedClosedGaussChosenRulingMatrix H I L hH hd hind hGauss 0 i) =
      g (e (closedGaussParameterNormal H I e i)) := by
  change σ (extendedClosedGaussRulingMatrix H I L
    (actualGaussRulingParameterChoice H I hH hd hind hGauss) 0 i) = _
  rw [extendedClosedGaussRulingMatrix_first_row_closed_normal H I L e, hσ]
  rfl

end DimensionFourDependence
