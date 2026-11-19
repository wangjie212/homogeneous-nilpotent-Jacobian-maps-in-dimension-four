import DimensionFourDependence.IndependentGaussRootConfigurationExclusion
import DimensionFourDependence.NativePencilSpreadFamily

/-! # Constructing the root divisor and its dense spread-out source image -/

namespace DimensionFourDependence

open MvPolynomial Matrix Module AlgebraicGeometry
open scoped TensorProduct

attribute [local instance] Algebra.TensorProduct.rightAlgebra
attribute [local instance] MvPolynomial.gradedAlgebra

universe u

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option quotPrecheck false

variable {K : Type u} [Field K] [CharZero K]
  (H : Fin 4 → MvPolynomial (Fin 4) K) (I : ImageRelationWitness H)
  (E : Type u) [Field E] [Algebra (closedGaussParameterField H I) E]
  [Algebra.IsAlgebraic (closedGaussParameterField H I) E]
  {d : ℕ} (hH : IsHomogMap H d)
  (e : RatFunc K ≃ₐ[K] closedGaussParameterField H I)

local notation "N" => extendedClosedGaussNormalizationScheme H I E hH e
local notation "m" => extendedClosedGaussNormalizationSourceMorphism H I E hH e
local notation "w" => extendedClosedGaussNormalizationHyperplaneWeight H I E hH e
local notation "T₀" a:max => projectiveCoordinateChartAlgebra (C := closedGaussParameterField H I)
  (rationalCoordinate (K := K) (n := 4)) ((finSuccEquiv' a).symm none) ⊗[closedGaussParameterField H I] E

local instance actualRootDivisorSpreadConstructionIntegral : IsIntegral N :=
  extendedClosedGaussNormalizationScheme_isIntegral H I E hH e
noncomputable local instance actualRootDivisorSpreadConstructionAlgebra : Algebra E (N).functionField :=
  extendedClosedGaussOwnFunctionFieldAlgebra H I E hH e

/-- Spreading out the closure of an actual native point has precisely
the closure of that point's original source image as its dense image. -/
theorem nativeClosedGaussPencilSpreadFamily_pointClosure_source_image
    (model : ClosedGaussParameterSchemeModel H I E) (z : N) :
    closure (Set.range (nativeClosedGaussPencilSpreadFamilySourceMorphism H I E hH e model
      (closure ({z} : Set N)) isIrreducible_singleton.closure)) =
        closure ({(m) z} : Set (AlgebraicGeometry.Proj (homogeneousSubmodule (Fin 4) K))) := by
  rw [nativeClosedGaussPencilSpreadFamilySourceMorphism_image_closure H I E hH e model
    (closure ({z} : Set N)) isIrreducible_singleton.closure isClosed_closure]
  exact (isGenericPoint_closure.image (m).continuous).def.symm

variable (hd : 0 < d) (hind : ¬ ComponentsDependent H) (hGauss : gaussImageDimension H I = 1)

local notation "ν₀" => extendedClosedGaussChosenRulingMatrix H I E hH hd hind hGauss 0

/-- The actual product-power data construct a zero divisor of U,
its original source divisor, and the entire integral spread-out family
with dense image in that source divisor. No zero prime or source-image
hypothesis is supplied. The closure of the exhibited point is the divisor. -/
theorem actual_native_gauss_root_combination_zero_divisor_with_dense_spread_source_image
    (cS cN : Fin 4 → E) (r : (N).functionField) (hr : r ≠ 0)
    (hroot : r ^ d = aeval w (extendedClosedGaussOutputLinearPolynomial H I E cS))
    (α β : E) (hα : α ≠ 0)
    (hprod : extendedClosedGaussHyperplaneGlobalValue H I E hH e
        (extendedClosedGaussRootCombinationSection H I E hH e ν₀ cS r hd hroot α β) *
          aeval w (extendedClosedGaussOutputLinearPolynomial H I E cN) = r ^ (d + 1)) :
    ∃ (a : Fin 4) (q : PrimeSpectrum (normalizationRing (T₀ a))),
      q.asIdeal.height = 1 ∧
      Order.coheight (extendedClosedGaussNormalizationTensorChartPoint H I E hH e (finSuccEquiv' a) q) = 1 ∧
      extendedClosedGaussHyperplaneGlobalCoefficientGerm H I E hH e
        (extendedClosedGaussRootCombinationSection H I E hH e ν₀ cS r hd hroot α β) a q ∈
        IsLocalRing.maximalIdeal ((N).presheaf.stalk
          (extendedClosedGaussNormalizationTensorChartPoint H I E hH e (finSuccEquiv' a) q)) ∧
      Order.coheight ((m) (extendedClosedGaussNormalizationTensorChartPoint H I E hH e (finSuccEquiv' a) q)) = 1 ∧
      ∀ model : ClosedGaussParameterSchemeModel H I E,
        closure (Set.range (nativeClosedGaussPencilSpreadFamilySourceMorphism H I E hH e model
          (closure ({extendedClosedGaussNormalizationTensorChartPoint H I E hH e (finSuccEquiv' a) q} : Set N))
          isIrreducible_singleton.closure)) =
        closure ({(m) (extendedClosedGaussNormalizationTensorChartPoint H I E hH e (finSuccEquiv' a) q)} :
          Set (AlgebraicGeometry.Proj (homogeneousSubmodule (Fin 4) K))) := by
  obtain ⟨a, q, hq, hcodim, hvan, _hsource⟩ :=
    actual_native_gauss_root_combination_zero_divisor_with_source_height_one H I E hH e hd hind hGauss
      cS cN r hr hroot α β hα hprod
  refine ⟨a, q, hq, hcodim, hvan, ?_, ?_⟩
  · exact actual_native_gauss_root_zero_source_coheight_one H I E hH e hd hind hGauss
      a q hq cS cN r hroot α β hα hprod hvan
  · intro model
    exact nativeClosedGaussPencilSpreadFamily_pointClosure_source_image H I E hH e model _

end DimensionFourDependence
