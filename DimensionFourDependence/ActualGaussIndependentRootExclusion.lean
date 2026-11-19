import DimensionFourDependence.ActualRootVanishingSourceDivisor
import DimensionFourDependence.NativeIndependentRulingExclusion

/-! # Independent ruling forms exclude every actual zero divisor without a source-image hypothesis -/

namespace DimensionFourDependence

open MvPolynomial Matrix Module AlgebraicGeometry
open scoped TensorProduct

attribute [local instance] MvPolynomial.gradedAlgebra Algebra.TensorProduct.rightAlgebra
attribute [local instance] tensorPencilResidueGenerationNormalizationRing
  tensorPencilResidueGenerationResidueField

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
  [Module.Finite (closedGaussParameterField H I) E]
  {d : ℕ} (hH : IsHomogMap H d)
  (e : RatFunc K ≃ₐ[K] closedGaussParameterField H I)
  (hd : 0 < d) (hind : ¬ ComponentsDependent H) (hGauss : gaussImageDimension H I = 1)

local notation "C₀" => closedGaussParameterField H I
local notation "T₀" a:max => projectiveCoordinateChartAlgebra (C := C₀)
  (rationalCoordinate (K := K) (n := 4)) ((finSuccEquiv' a).symm none) ⊗[C₀] E
local notation "N" => extendedClosedGaussNormalizationScheme H I E hH e
local notation "V" a:max => extendedClosedGaussNormalizationChartOpen H I E hH e (finSuccEquiv' a)
local notation "w" => extendedClosedGaussNormalizationHyperplaneWeight H I E hH e
local notation "ν₀" => extendedClosedGaussChosenRulingMatrix H I E hH hd hind hGauss 0
local notation "W₀" => LinearMap.ker
  (extendedClosedGaussChosenRulingMatrix H I E hH hd hind hGauss).toLin'

local instance actualGaussIndependentRootExclusionIntegral : IsIntegral N :=
  extendedClosedGaussNormalizationScheme_isIntegral H I E hH e
noncomputable local instance actualGaussIndependentRootExclusionAlgebra : Algebra E (N).functionField :=
  extendedClosedGaussOwnFunctionFieldAlgebra H I E hH e

/-- In the actual independent m,n branch, a given zero divisor of
U is impossible. Actual tangent-plane incidence supplies its source
divisor image internally. No dense image, source codimension, component
span, reduced pencil presentation, common factor, or degree bound is supplied. -/
theorem no_actual_independent_gauss_rational_root_zero_divisor
    (a : Fin 4) (q : PrimeSpectrum (normalizationRing (T₀ a))) (hq : q.asIdeal.height = 1)
    (cS cM cN : Fin 4 → E) (r : (N).functionField) (hr : r ≠ 0)
    (hroot : r ^ d = aeval w (extendedClosedGaussOutputLinearPolynomial H I E cS))
    (α β : E) (hα : α ≠ 0)
    (hMN : LinearIndependent E ![rulingFormRestriction W₀ cM, rulingFormRestriction W₀ cN])
    (hlinear : rulingFormRestriction W₀ cS = α • rulingFormRestriction W₀ cM +
      β • rulingFormRestriction W₀ cN)
    (hm : aeval w (extendedClosedGaussOutputLinearPolynomial H I E cM) ≠ 0)
    (hformula : r = aeval w (extendedClosedGaussOutputLinearPolynomial H I E cN) *
      (∑ i, algebraMap E (N).functionField (ν₀ i) * w i) /
        aeval w (extendedClosedGaussOutputLinearPolynomial H I E cM))
    (hvan : extendedClosedGaussHyperplaneGlobalCoefficientGerm H I E hH e
      (extendedClosedGaussRootCombinationSection H I E hH e ν₀ cS r hd hroot α β) a q ∈
        IsLocalRing.maximalIdeal ((N).presheaf.stalk
          (extendedClosedGaussNormalizationTensorChartPoint H I E hH e (finSuccEquiv' a) q))) : False := by
  have hSN := independent_ruling_forms_of_nonzero_binary_coefficient
    (rulingFormRestriction W₀ cS) (rulingFormRestriction W₀ cM)
    (rulingFormRestriction W₀ cN) α β hα hMN hlinear
  obtain ⟨bS, bN, hspan⟩ := extendedClosedGauss_native_output_span_of_chosen_ruling_forms
    H I E hH e hd hind hGauss cS cN hSN
  have hvalue := extendedClosedGauss_chosen_ruling_binary_output_relation
    H I E hH e hd hind hGauss cS cM cN α β hlinear
  have hprod := actual_native_root_combination_product_power_of_rational_root_formula H I E hH e
    ν₀ cS cM cN r hd hroot α β hvalue hm hformula
  have hcodim := actual_native_gauss_root_zero_source_coheight_one H I E hH e hd hind hGauss
    a q hq cS cN r hroot α β hα hprod hvan
  obtain ⟨p, q₀, D, _hD, _hp, hq₀, hpH, hqH, hrel, ht⟩ :=
    actual_closed_gauss_parameter_reduced_homogeneous_source_quotient H hH I e
  obtain ⟨g, P, c, _hc, hg, hgh, hP, hprim, hHP, _hPdeg⟩ :=
    exists_primitive_factorization_common_degree_le_sub_two H hH hind I
  rw [extendedClosedGaussRootCombinationSection_value] at hprod
  exact no_actual_nonplanar_native_pencil_output_span_source_divisor H I E hH e hGauss
    p q₀ hq₀ hrel hpH hqH ht hind ν₀ cS cN r hr hd hroot α β hprod bS bN hspan
    (extendedClosedGaussNormalizationTensorChartPoint H I E hH e (finSuccEquiv' a) q) hcodim a
    (extendedClosedGaussNormalizationTensorChartPoint_mem_chart H I E hH e (finSuccEquiv' a) q) hvan
    P g hg hgh hP hprim hHP

end DimensionFourDependence
