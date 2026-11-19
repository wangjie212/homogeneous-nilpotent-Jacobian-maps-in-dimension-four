import DimensionFourDependence.NativeChosenRootForms
import DimensionFourDependence.TwoDimensionalFormAlternatives
import DimensionFourDependence.RulingFormNonvanishing
import DimensionFourDependence.IndependentGaussRootConfigurationExclusion

/-! # The actual root forms satisfy the paper's two remaining ruling alternatives

The original nonzero root and rational formula make all three forms
nonzero on the actual ruling. Its dual has dimension two, so the binary
relation is constructed. A nonzero first coefficient is excluded by the
checked divisor argument. Only the two proportional cases remain.
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

local instance actualChosenRootAlternativesIntegral : IsIntegral N :=
  extendedClosedGaussNormalizationScheme_isIntegral H I E hH e
noncomputable local instance actualChosenRootAlternativesAlgebra : Algebra E (N).functionField :=
  extendedClosedGaussOwnFunctionFieldAlgebra H I E hH e

/-- The exact two remaining alternatives of Section 4.2, on the
actual chosen ruling. All proportionality coefficients are nonzero. -/
noncomputable def ChosenGaussRulingFormAlternatives (cS cM cN : Fin 4 → E) : Prop :=
  (∃ γ : E, γ ≠ 0 ∧ (R) cM = γ • (R) cN) ∨
    (LinearIndependent E ![(R) cM, (R) cN] ∧ ∃ β : E, β ≠ 0 ∧ (R) cS = β • (R) cN)

/-- Actual root data together with the two proved remaining
ruling-form alternatives. The independent binary branch is absent. -/
noncomputable def ActualChosenGaussRationalRootAlternatives : Prop :=
  ∃ (cS cM cN : Fin 4 → E) (r : (N).functionField),
    cS ≠ 0 ∧ cM ≠ 0 ∧ cN ≠ 0 ∧ r ≠ 0 ∧
      r ^ d = aeval (w) ((O) cS) ∧ aeval (w) ((O) cM) ≠ 0 ∧
      r = aeval (w) ((O) cN) * (∑ i, algebraMap E (N).functionField ((ν₀) i) * (w) i) /
        aeval (w) ((O) cM) ∧
      ChosenGaussRulingFormAlternatives H I E hH hd hind hGauss cS cM cN ∧
      HasActualGaussRootNumerator H I E e cN

variable [Module.Finite (closedGaussParameterField H I) E]

/-- The actual rational root forms give the two proportional
alternatives. Their binary relation, nonzero restricted forms and
independent-branch divisor contradiction are all derived internally. -/
theorem actual_chosen_root_forms_have_two_ruling_alternatives
    (cS cM cN : Fin 4 → E) (r : (N).functionField) (hr : r ≠ 0)
    (hroot : r ^ d = aeval (w) ((O) cS)) (hm : aeval (w) ((O) cM) ≠ 0)
    (hformula : r = aeval (w) ((O) cN) *
      (∑ i, algebraMap E (N).functionField ((ν₀) i) * (w) i) / aeval (w) ((O) cM)) :
    ChosenGaussRulingFormAlternatives H I E hH hd hind hGauss cS cM cN := by
  have hS : (R) cS ≠ 0 := extendedClosedGauss_ruling_form_ne_zero_of_native_output_ne_zero
    H I E hH e hd hind hGauss cS (hroot ▸ pow_ne_zero d hr)
  have hM : (R) cM ≠ 0 := extendedClosedGauss_ruling_form_ne_zero_of_native_output_ne_zero
    H I E hH e hd hind hGauss cM hm
  have hNvalue : aeval (w) ((O) cN) ≠ 0 := by
    intro hz
    apply hr
    rw [hformula, hz, zero_mul, zero_div]
  have hN : (R) cN ≠ 0 := extendedClosedGauss_ruling_form_ne_zero_of_native_output_ne_zero
    H I E hH e hd hind hGauss cN hNvalue
  have hdim : finrank E (Module.Dual E (W₀)) = 2 := by
    rw [Subspace.dual_finrank_eq, extendedClosedGaussChosenRulingMatrix_kernel_finrank H I E hH hd hind hGauss]
  rcases two_dimensional_form_three_alternatives hdim ((R) cM) ((R) cN) ((R) cS) hN with
    ⟨γ, hγ⟩ | ⟨hMN, β, hβ⟩ | ⟨hMN, α, β, hα, hlinear⟩
  · refine Or.inl ⟨γ, ?_, hγ⟩
    intro hz
    exact hM (by simpa only [hz, zero_smul] using hγ)
  · refine Or.inr ⟨hMN, β, ?_, hβ⟩
    intro hz
    exact hS (by simpa only [hz, zero_smul] using hβ)
  · exact (no_actual_independent_gauss_rational_root_configuration H I E hH e hd hind hGauss
      cS cM cN r hr hroot α β hα hMN hlinear hm hformula).elim

/-- The actual chosen-plane root data construct the paper's
remaining two cases, without a supplied binary-form relation. -/
theorem actual_chosen_root_data_construct_two_alternatives
    (hdata : ActualChosenGaussRationalRootData H I E hH e hd hind hGauss) :
    ActualChosenGaussRationalRootAlternatives H I E hH e hd hind hGauss := by
  obtain ⟨cS, cM, cN, r, hS, hM, hN, hr, hroot, hm, hformula, hnumerator⟩ := hdata
  exact ⟨cS, cM, cN, r, hS, hM, hN, hr, hroot, hm, hformula,
    actual_chosen_root_forms_have_two_ruling_alternatives H I E hH e hd hind hGauss
      cS cM cN r hr hroot hm hformula, hnumerator⟩

end DimensionFourDependence
