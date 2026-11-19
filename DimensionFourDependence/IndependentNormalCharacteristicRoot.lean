import DimensionFourDependence.IndependentNormalScaledPowerExclusion
import DimensionFourDependence.NativeProportionalPowerFactorization

/-! # Independent original normals leave only the characteristic root factorization -/

namespace DimensionFourDependence

open MvPolynomial Matrix AlgebraicGeometry

universe u

set_option quotPrecheck false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000

variable {K : Type u} [Field K] [CharZero K]
    (H : Fin 4 → MvPolynomial (Fin 4) K) (I : ImageRelationWitness H)
    (E : Type u) [Field E] [Algebra (closedGaussParameterField H I) E]
    [Algebra.IsAlgebraic (closedGaussParameterField H I) E]
    {d : ℕ} (hH : IsHomogMap H d) (e : RatFunc K ≃ₐ[K] closedGaussParameterField H I)
    (hd : 0 < d) (hind : ¬ComponentsDependent H) (hGauss : gaussImageDimension H I = 1)

local notation "N" => extendedClosedGaussNormalizationScheme H I E hH e
local notation "w" => extendedClosedGaussNormalizationHyperplaneWeight H I E hH e
local notation "A₀" => extendedClosedGaussChosenRulingMatrix H I E hH hd hind hGauss
local notation "W₀" => LinearMap.ker (A₀).toLin'
local notation "O" => extendedClosedGaussOutputLinearPolynomial H I E
local notation "R" => rulingFormRestriction (W₀)
local notation "Lₜ" => ∑ i, algebraMap E (N).functionField ((A₀) 0 i) * (w) i

local instance independentNormalCharacteristicRootIntegral : IsIntegral N :=
  extendedClosedGaussNormalizationScheme_isIntegral H I E hH e
noncomputable local instance independentNormalCharacteristicRootAlgebra : Algebra E (N).functionField :=
  extendedClosedGaussOwnFunctionFieldAlgebra H I E hH e

/-- The original root equations with only the characteristic case:
m,n independent, s proportional to n, and the exact factorization
whose distinguished vector spans the actual chosen characteristic. -/
noncomputable def ActualCharacteristicGaussRootData : Prop :=
  ∃ (cS cM cN : Fin 4 → E) (r : (N).functionField),
    cS ≠ 0 ∧ cM ≠ 0 ∧ cN ≠ 0 ∧ r ≠ 0 ∧ r ^ d = aeval (w) ((O) cS) ∧
      aeval (w) ((O) cM) ≠ 0 ∧
      r = aeval (w) ((O) cN) * (Lₜ) / aeval (w) ((O) cM) ∧
      LinearIndependent E ![(R) cM, (R) cN] ∧
      (∃ β : E, β ≠ 0 ∧ (R) cS = β • (R) cN) ∧
      CharacteristicNativeRulingRootFactorization H I E hH e hd hind hGauss cN r ∧
      HasActualGaussRootNumerator H I E e cN

/-- The checked scaled-plane contradiction removes the first
remaining native root case without assuming a base point or power congruence. -/
theorem independent_normal_root_forms_construct_characteristic_factorization
    (hNormal : LinearIndependent K (rationalImageNormal H I.equation))
    (hdata : ActualChosenGaussRootNormalForms H I E hH e hd hind hGauss) :
    ActualCharacteristicGaussRootData H I E hH e hd hind hGauss := by
  obtain ⟨cS, cM, cN, r, hS, hM, hN, hr, hroot, hm, hformula, halt, hnumerator⟩ := hdata
  rcases halt with ⟨γ, hγ, hMN, _hplane, _hpower⟩ | ⟨hMN, β, hβ, hSN, hfactor⟩
  · exact False.elim (no_actual_proportional_root_denominator_for_independent_normal
      H I E hd hH hind hGauss hNormal e cS cM cN r hr hroot γ hγ hMN hformula)
  · exact ⟨cS, cM, cN, r, hS, hM, hN, hr, hroot, hm, hformula, hMN, ⟨β, hβ, hSN⟩,
      hfactor, hnumerator⟩

end DimensionFourDependence
