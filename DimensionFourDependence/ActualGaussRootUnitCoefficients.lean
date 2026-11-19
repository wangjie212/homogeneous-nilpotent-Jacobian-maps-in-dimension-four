import DimensionFourDependence.ActualGaussIndependentRootExclusion
import DimensionFourDependence.ExtendedNonunitSectionDivisor

/-! # The independent ruling-root configuration forces every actual section coefficient to be a unit -/

namespace DimensionFourDependence

open MvPolynomial Matrix Module AlgebraicGeometry
open scoped TensorProduct

attribute [local instance] MvPolynomial.gradedAlgebra Algebra.TensorProduct.rightAlgebra

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
local notation "w" => extendedClosedGaussNormalizationHyperplaneWeight H I E hH e

local instance actualGaussRootUnitCoefficientsIntegral : IsIntegral N :=
  extendedClosedGaussNormalizationScheme_isIntegral H I E hH e
noncomputable local instance actualGaussRootUnitCoefficientsAlgebra : Algebra E (N).functionField :=
  extendedClosedGaussOwnFunctionFieldAlgebra H I E hH e

/-- The original nonzero root and actual product-power equation
derive nonvanishing of U as an actual global regular section. -/
theorem actual_native_root_combination_ne_zero_of_product_power
    (ν cS cN : Fin 4 → E) (r : (N).functionField) (hr : r ≠ 0) (hd : 0 < d)
    (hroot : r ^ d = aeval w (extendedClosedGaussOutputLinearPolynomial H I E cS))
    (α β : E)
    (hprod : extendedClosedGaussHyperplaneGlobalValue H I E hH e
        (extendedClosedGaussRootCombinationSection H I E hH e ν cS r hd hroot α β) *
          aeval w (extendedClosedGaussOutputLinearPolynomial H I E cN) = r ^ (d + 1)) :
    extendedClosedGaussRootCombinationSection H I E hH e ν cS r hd hroot α β ≠ 0 := by
  have hu : extendedClosedGaussHyperplaneGlobalValue H I E hH e
      (extendedClosedGaussRootCombinationSection H I E hH e ν cS r hd hroot α β) ≠ 0 :=
    (mul_ne_zero_iff.mp (hprod ▸ pow_ne_zero (d + 1) hr)).1
  intro hzero
  apply hu
  rw [hzero]
  rfl

variable [Module.Finite (closedGaussParameterField H I) E]
  (hd : 0 < d) (hind : ¬ ComponentsDependent H) (hGauss : gaussImageDimension H I = 1)

local notation "ν₀" => extendedClosedGaussChosenRulingMatrix H I E hH hd hind hGauss 0
local notation "W₀" => LinearMap.ker
  (extendedClosedGaussChosenRulingMatrix H I E hH hd hind hGauss).toLin'

/-- In the independent m,n branch, the actual root combination has
an invertible regular coefficient in every original coordinate chart.
A nonunit coefficient would construct a divisor that the original
ruling-root configuration excludes; no zero prime or source-image data
are hypotheses. The remaining global nontriviality obstruction is separate. -/
theorem actual_independent_gauss_rational_root_combination_coefficient_isUnit
    (cS cM cN : Fin 4 → E) (r : (N).functionField) (hr : r ≠ 0)
    (hroot : r ^ d = aeval w (extendedClosedGaussOutputLinearPolynomial H I E cS))
    (α β : E) (hα : α ≠ 0)
    (hMN : LinearIndependent E ![rulingFormRestriction W₀ cM, rulingFormRestriction W₀ cN])
    (hlinear : rulingFormRestriction W₀ cS = α • rulingFormRestriction W₀ cM +
      β • rulingFormRestriction W₀ cN)
    (hm : aeval w (extendedClosedGaussOutputLinearPolynomial H I E cM) ≠ 0)
    (hformula : r = aeval w (extendedClosedGaussOutputLinearPolynomial H I E cN) *
      (∑ i, algebraMap E (N).functionField (ν₀ i) * w i) /
        aeval w (extendedClosedGaussOutputLinearPolynomial H I E cM)) (a : Fin 4) :
    IsUnit (extendedClosedGaussHyperplaneGlobalCoefficient H I E hH e
      (extendedClosedGaussRootCombinationSection H I E hH e ν₀ cS r hd hroot α β) a) := by
  have hvalue := extendedClosedGauss_chosen_ruling_binary_output_relation
    H I E hH e hd hind hGauss cS cM cN α β hlinear
  have hprod := actual_native_root_combination_product_power_of_rational_root_formula H I E hH e
    ν₀ cS cM cN r hd hroot α β hvalue hm hformula
  have hne := actual_native_root_combination_ne_zero_of_product_power H I E hH e
    ν₀ cS cN r hr hd hroot α β hprod
  apply (actual_native_section_coefficient_isUnit_iff_no_zero_divisor H I E hH e
    (extendedClosedGaussRootCombinationSection H I E hH e ν₀ cS r hd hroot α β) hne a).mpr
  intro q hq hvan
  exact no_actual_independent_gauss_rational_root_zero_divisor H I E hH e hd hind hGauss
    a q hq cS cM cN r hr hroot α β hα hMN hlinear hm hformula hvan

end DimensionFourDependence
