import DimensionFourDependence.ExtendedNativeConeZeroTransfer
import DimensionFourDependence.NativeIndependentRulingExclusion

/-! # The actual independent ruling-root configuration is excluded without a given zero divisor -/

namespace DimensionFourDependence

open MvPolynomial Matrix Module AlgebraicGeometry
open scoped TensorProduct

attribute [local instance] Algebra.TensorProduct.rightAlgebra

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
  (hd : 0 < d) (hind : ¬ ComponentsDependent H) (hGauss : gaussImageDimension H I = 1)

local notation "C₀" => closedGaussParameterField H I
local notation "N" => extendedClosedGaussNormalizationScheme H I E hH e
local notation "w" => extendedClosedGaussNormalizationHyperplaneWeight H I E hH e
local notation "ν₀" => extendedClosedGaussChosenRulingMatrix H I E hH hd hind hGauss 0
local notation "W₀" => LinearMap.ker
  (extendedClosedGaussChosenRulingMatrix H I E hH hd hind hGauss).toLin'
local notation "T₀" a:max => projectiveCoordinateChartAlgebra (C := C₀)
  (rationalCoordinate (K := K) (n := 4)) ((finSuccEquiv' a).symm none) ⊗[C₀] E

local instance independentGaussRootConfigurationExclusionIntegral : IsIntegral N :=
  extendedClosedGaussNormalizationScheme_isIntegral H I E hH e
noncomputable local instance independentGaussRootConfigurationExclusionAlgebra : Algebra E (N).functionField :=
  extendedClosedGaussOwnFunctionFieldAlgebra H I E hH e

/-- The actual root-combination zero divisor is constructed and its
actual original source contraction has codimension one. Neither a zero
prime, Gauss-plane incidence, nor a source-image condition is supplied. -/
theorem actual_native_gauss_root_combination_zero_divisor_with_source_height_one
    (cS cN : Fin 4 → E) (r : (N).functionField) (hr : r ≠ 0)
    (hroot : r ^ d = aeval w (extendedClosedGaussOutputLinearPolynomial H I E cS))
    (α β : E) (hα : α ≠ 0)
    (hprod : extendedClosedGaussHyperplaneGlobalValue H I E hH e
        (extendedClosedGaussRootCombinationSection H I E hH e ν₀ cS r hd hroot α β) *
          aeval w (extendedClosedGaussOutputLinearPolynomial H I E cN) = r ^ (d + 1)) :
    ∃ (a : Fin 4) (q : PrimeSpectrum (normalizationRing (T₀ a))), q.asIdeal.height = 1 ∧
      Order.coheight (extendedClosedGaussNormalizationTensorChartPoint H I E hH e (finSuccEquiv' a) q) = 1 ∧
      extendedClosedGaussHyperplaneGlobalCoefficientGerm H I E hH e
        (extendedClosedGaussRootCombinationSection H I E hH e ν₀ cS r hd hroot α β) a q ∈
        IsLocalRing.maximalIdeal ((N).presheaf.stalk
          (extendedClosedGaussNormalizationTensorChartPoint H I E hH e (finSuccEquiv' a) q)) ∧
      (q.asIdeal.comap (extendedClosedGaussTensorNormalizationSourceHom H I E (finSuccEquiv' a))).height = 1 := by
  obtain ⟨a, q, hq, hcodim, hvan⟩ := actual_native_root_combination_has_zero_divisor_of_product_power H I E hH e
    hGauss ν₀ cS cN r hr hd hroot α β hprod
  exact ⟨a, q, hq, hcodim, hvan, actual_native_gauss_root_zero_source_prime_height_one H I E hH e hd hind hGauss
    a q hq cS cN r hroot α β hα hprod hvan⟩

variable [Module.Finite (closedGaussParameterField H I) E]

/-- The actual independent m,n branch of (4.4) is impossible from
its original rational root and ruling-restricted binary-form data alone.
The actual zero divisor of U, original Gauss-plane incidence, source
divisor image, component span, local multiplicities, pencil degree and
common-factor contradiction are all constructed internally. -/
theorem no_actual_independent_gauss_rational_root_configuration
    (cS cM cN : Fin 4 → E) (r : (N).functionField) (hr : r ≠ 0)
    (hroot : r ^ d = aeval w (extendedClosedGaussOutputLinearPolynomial H I E cS))
    (α β : E) (hα : α ≠ 0)
    (hMN : LinearIndependent E ![rulingFormRestriction W₀ cM, rulingFormRestriction W₀ cN])
    (hlinear : rulingFormRestriction W₀ cS = α • rulingFormRestriction W₀ cM +
      β • rulingFormRestriction W₀ cN)
    (hm : aeval w (extendedClosedGaussOutputLinearPolynomial H I E cM) ≠ 0)
    (hformula : r = aeval w (extendedClosedGaussOutputLinearPolynomial H I E cN) *
      (∑ i, algebraMap E (N).functionField (ν₀ i) * w i) /
        aeval w (extendedClosedGaussOutputLinearPolynomial H I E cM)) : False := by
  have hvalue := extendedClosedGauss_chosen_ruling_binary_output_relation
    H I E hH e hd hind hGauss cS cM cN α β hlinear
  have hprod := actual_native_root_combination_product_power_of_rational_root_formula H I E hH e
    ν₀ cS cM cN r hd hroot α β hvalue hm hformula
  obtain ⟨a, q, hq, _hcodim, hvan⟩ := actual_native_root_combination_has_zero_divisor_of_product_power H I E hH e
    hGauss ν₀ cS cN r hr hd hroot α β hprod
  exact no_actual_independent_gauss_rational_root_zero_divisor H I E hH e hd hind hGauss
    a q hq cS cM cN r hr hroot α β hα hMN hlinear hm hformula hvan

end DimensionFourDependence
