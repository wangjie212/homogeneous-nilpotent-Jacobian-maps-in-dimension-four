import DimensionFourDependence.ActualChosenRootAlternatives

/-! # The actual independent root forms construct the section identity (4.5)

The actual ruling dual has dimension two. Independent denominator and
numerator forms therefore construct the binary coefficients of the
root-power form. Their relation gives the actual regular root-combination
section identity without a supplied binary relation or product identity.
-/

namespace DimensionFourDependence

open MvPolynomial Matrix Module AlgebraicGeometry

universe u

set_option quotPrecheck false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

variable {K : Type u} [Field K] [CharZero K]
    (H : Fin 4 → MvPolynomial (Fin 4) K) (I : ImageRelationWitness H)
    (E : Type u) [Field E] [Algebra (closedGaussParameterField H I) E]
    [Algebra.IsAlgebraic (closedGaussParameterField H I) E]
    {d : ℕ} (hH : IsHomogMap H d) (e : RatFunc K ≃ₐ[K] closedGaussParameterField H I)
    (hd : 0 < d) (hind : ¬ ComponentsDependent H) (hGauss : gaussImageDimension H I = 1)

local notation "N" => extendedClosedGaussNormalizationScheme H I E hH e
local notation "w" => extendedClosedGaussNormalizationHyperplaneWeight H I E hH e
local notation "ν₀" => extendedClosedGaussChosenRulingMatrix H I E hH hd hind hGauss 0
local notation "W₀" => LinearMap.ker (extendedClosedGaussChosenRulingMatrix H I E hH hd hind hGauss).toLin'
local notation "O" => extendedClosedGaussOutputLinearPolynomial H I E
local notation "R" => rulingFormRestriction (W₀)

local instance constructedRulingProductPowerIntegral : IsIntegral N :=
  extendedClosedGaussNormalizationScheme_isIntegral H I E hH e
noncomputable local instance constructedRulingProductPowerAlgebra : Algebra E (N).functionField :=
  extendedClosedGaussOwnFunctionFieldAlgebra H I E hH e

/-- Actual independent root forms construct their binary relation
and the regular section identity (4.5). Neither the binary coefficients
nor a binary relation nor the product-power identity is assumed. -/
theorem actual_chosen_independent_root_forms_construct_product_power
    (cS cM cN : Fin 4 → E) (r : (N).functionField)
    (hroot : r ^ d = aeval (w) ((O) cS))
    (hMN : LinearIndependent E ![(R) cM, (R) cN])
    (hm : aeval (w) ((O) cM) ≠ 0)
    (hformula : r = aeval (w) ((O) cN) *
      (∑ i, algebraMap E (N).functionField ((ν₀) i) * (w) i) / aeval (w) ((O) cM)) :
    ∃ α β : E, (R) cS = α • (R) cM + β • (R) cN ∧
      extendedClosedGaussHyperplaneGlobalValue H I E hH e
        (extendedClosedGaussRootCombinationSection H I E hH e (ν₀) cS r hd hroot α β) *
          aeval (w) ((O) cN) = r ^ (d + 1) := by
  have hdim : finrank E (Module.Dual E (W₀)) = 2 := by
    rw [Subspace.dual_finrank_eq, extendedClosedGaussChosenRulingMatrix_kernel_finrank H I E hH hd hind hGauss]
  obtain ⟨α, β, hlinear⟩ := two_dimensional_independent_pair_binary_span hdim ((R) cM) ((R) cN) ((R) cS) hMN
  have hvalue := extendedClosedGauss_chosen_ruling_binary_output_relation H I E hH e hd hind hGauss cS cM cN α β hlinear
  exact ⟨α, β, hlinear,
    actual_native_root_combination_product_power_of_rational_root_formula H I E hH e
      (ν₀) cS cM cN r hd hroot α β hvalue hm hformula⟩

end DimensionFourDependence
