import DimensionFourDependence.NativeProportionalRootIdentities
import DimensionFourDependence.RulingCoordinateBasis
import DimensionFourDependence.ActualRootCharacteristicComparison

/-! # The two remaining native root cases construct their algebraic normal forms

In the second case the actual ruling dual supplies independent original
coefficient vectors. Their exact dual pairings put one vector in the
numerator kernel. The root equations give the native component
factorization H=rho^(d-1)(rho V+L_t W), with both vectors in the actual
ruling. The exact retained second-normal provenance identifies the
distinguished vector with the original chosen characteristic line.
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
local notation "A₀" => extendedClosedGaussChosenRulingMatrix H I E hH hd hind hGauss
local notation "W₀" => LinearMap.ker (A₀).toLin'
local notation "O" => extendedClosedGaussOutputLinearPolynomial H I E
local notation "R" => rulingFormRestriction (W₀)
local notation "Lₜ" => ∑ i, algebraMap E (N).functionField ((A₀) 0 i) * (w) i
local notation "Y₀" => fun i => aeval (w) (MvPolynomial.map (extendedClosedGaussSourceCoefficientHom H I E) (H i))

local instance nativeProportionalPowerFactorizationIntegral : IsIntegral N :=
  extendedClosedGaussNormalizationScheme_isIntegral H I E hH e
noncomputable local instance nativeProportionalPowerFactorizationAlgebra : Algebra E (N).functionField :=
  extendedClosedGaussOwnFunctionFieldAlgebra H I E hH e

/-- The actual independent ruling vectors and native component
factorization in the second remaining case. The second vector lies in
the original numerator kernel on the actual ruling. -/
noncomputable def NativeRulingRootFactorization (cN : Fin 4 → E) (r : (N).functionField) : Prop :=
  ∃ V W : Fin 4 → E, LinearIndependent E ![V, W] ∧ V ∈ (W₀) ∧ W ∈ (W₀) ∧ cN ⬝ᵥ W = 0 ∧
    ∀ i, (Y₀) i = r ^ (d - 1) * (r * algebraMap E (N).functionField (V i) +
      (Lₜ) * algebraMap E (N).functionField (W i))

/-- The actual factorization with its distinguished vector spanning
exactly the original chosen Gauss characteristic line. -/
noncomputable def CharacteristicNativeRulingRootFactorization
    (cN : Fin 4 → E) (r : (N).functionField) : Prop :=
  ∃ V W : Fin 4 → E, LinearIndependent E ![V, W] ∧ V ∈ (W₀) ∧ W ∈ (W₀) ∧
    W ∈ extendedClosedGaussChosenCharacteristicSubspace H I E hH hd hind hGauss ∧
    Submodule.span E {W} = extendedClosedGaussChosenCharacteristicSubspace H I E hH hd hind hGauss ∧
    cN ⬝ᵥ W = 0 ∧
    ∀ i, (Y₀) i = r ^ (d - 1) * (r * algebraMap E (N).functionField (V i) +
      (Lₜ) * algebraMap E (N).functionField (W i))

/-- Independent m,n and proportional s,n construct the actual
independent ruling vectors and the native factorization (4.6). No
component-span coefficients or factorization vectors are supplied. -/
theorem native_proportional_power_constructs_ruling_factorization
    (cS cM cN : Fin 4 → E) (r : (N).functionField) (hr : r ≠ 0)
    (hroot : r ^ d = aeval (w) ((O) cS)) (hm : aeval (w) ((O) cM) ≠ 0)
    (hMN : LinearIndependent E ![(R) cM, (R) cN])
    (β : E) (hβ : β ≠ 0) (hSN : (R) cS = β • (R) cN)
    (hformula : r = aeval (w) ((O) cN) * (Lₜ) / aeval (w) ((O) cM)) :
    NativeRulingRootFactorization H I E hH e hd hind hGauss cN r := by
  obtain ⟨bM, bN, hB, hbM, hbN, _hMbM, hNbM, _hMbN, _hNbN, hspan⟩ :=
    two_dimensional_ruling_coordinate_basis (W₀)
      (extendedClosedGaussChosenRulingMatrix_kernel_finrank H I E hH hd hind hGauss) cM cN hMN
  have hcoordinate (i : Fin 4) : (Y₀) i =
      algebraMap E (N).functionField (bM i) * aeval (w) ((O) cM) +
        algebraMap E (N).functionField (bN i) * aeval (w) ((O) cN) := by
    have hi := matrix_kernel_coordinate_form_span_after_extension (E := (N).functionField)
      (A₀) cM cN bM bN hspan (Y₀)
      (extendedClosedGauss_native_output_mem_chosen_ruling H I E hH e hd hind hGauss) i
    simpa only [dotProduct, ← extendedClosedGaussOutputLinearPolynomial_value H I E hH e cM,
      ← extendedClosedGaussOutputLinearPolynomial_value H I E hH e cN] using hi
  have hvalues : aeval (w) ((O) cN) = algebraMap E (N).functionField β⁻¹ * r ^ d ∧
      aeval (w) ((O) cM) = algebraMap E (N).functionField β⁻¹ * r ^ (d - 1) * (Lₜ) :=
    native_root_proportional_power_output_values H I E hH e hd hind hGauss cS cM cN r hr hroot hm β hβ hSN hformula
  have hunit : IsUnit β⁻¹ := isUnit_iff_ne_zero.mpr (inv_ne_zero hβ)
  have hLI : LinearIndependent E ![β⁻¹ • bN, β⁻¹ • bM] :=
    (LinearIndependent.pair_smul_smul_iff hunit hunit).mpr (LinearIndependent.pair_symm_iff.mp hB)
  refine ⟨β⁻¹ • bN, β⁻¹ • bM, hLI, (W₀).smul_mem _ hbN, (W₀).smul_mem _ hbM, ?_, ?_⟩
  · simp only [dotProduct_smul, smul_eq_mul, hNbM, mul_zero]
  · intro i
    have hpow : r ^ d = r ^ (d - 1) * r := by
      rw [← pow_succ]
      congr 1
      omega
    rw [hcoordinate i, hvalues.1, hvalues.2, hpow]
    simp only [Pi.smul_apply, smul_eq_mul, map_mul]
    ring

/-- The exact retained numerator provenance identifies the
distinguished nonzero factorization vector with the actual characteristic
point. No characteristic-direction hypothesis is supplied. -/
theorem actual_ruling_root_factorization_constructs_characteristic_direction
    (cN : Fin 4 → E) (r : (N).functionField)
    (hN : HasActualGaussRootNumerator H I E e cN)
    (hfactor : NativeRulingRootFactorization H I E hH e hd hind hGauss cN r) :
    CharacteristicNativeRulingRootFactorization H I E hH e hd hind hGauss cN r := by
  obtain ⟨V, W, hLI, hV, hW, hzero, hvalue⟩ := hfactor
  have hW0 : W ≠ 0 := by simpa using hLI.ne_zero (1 : Fin 2)
  have hchar := (actual_gauss_root_numerator_zero_iff_characteristic H I E e hH hd hind hGauss cN hN W hW).mp hzero
  have hspan := actual_gauss_root_numerator_zero_direction_spans_characteristic H I E e hH hd hind hGauss
    cN hN W hW0 hW hzero
  exact ⟨V, W, hLI, hV, hW, hchar, hspan, hzero, hvalue⟩

/-- The actual remaining alternatives with their exact algebraic
root identities and, in the second case, constructed ruling vectors. -/
noncomputable def NativeRootRemainingCaseNormalForms
    (cS cM cN : Fin 4 → E) (r : (N).functionField) : Prop :=
  (∃ γ : E, γ ≠ 0 ∧ (R) cM = γ • (R) cN ∧
    r = algebraMap E (N).functionField γ⁻¹ * (Lₜ) ∧
    aeval (w) ((O) cS) = (algebraMap E (N).functionField γ⁻¹) ^ d * (Lₜ) ^ d) ∨
  (LinearIndependent E ![(R) cM, (R) cN] ∧
    ∃ β : E, β ≠ 0 ∧ (R) cS = β • (R) cN ∧
      CharacteristicNativeRulingRootFactorization H I E hH e hd hind hGauss cN r)

/-- Actual root data with both proportional alternatives reduced
to their actual native algebraic normal forms. -/
noncomputable def ActualChosenGaussRootNormalForms : Prop :=
  ∃ (cS cM cN : Fin 4 → E) (r : (N).functionField),
    cS ≠ 0 ∧ cM ≠ 0 ∧ cN ≠ 0 ∧ r ≠ 0 ∧ r ^ d = aeval (w) ((O) cS) ∧
      aeval (w) ((O) cM) ≠ 0 ∧
      r = aeval (w) ((O) cN) * (Lₜ) / aeval (w) ((O) cM) ∧
      NativeRootRemainingCaseNormalForms H I E hH e hd hind hGauss cS cM cN r ∧
      HasActualGaussRootNumerator H I E e cN

/-- The two proved remaining actual root alternatives construct
the exact plane-power case or the independent-vector factorization. -/
theorem actual_chosen_root_alternatives_construct_native_normal_forms
    (hdata : ActualChosenGaussRationalRootAlternatives H I E hH e hd hind hGauss) :
    ActualChosenGaussRootNormalForms H I E hH e hd hind hGauss := by
  obtain ⟨cS, cM, cN, r, hS, hM, hN, hr, hroot, hm, hformula, halt, hnumerator⟩ := hdata
  refine ⟨cS, cM, cN, r, hS, hM, hN, hr, hroot, hm, hformula, ?_, hnumerator⟩
  rcases halt with ⟨γ, hγ, hMN⟩ | ⟨hMN, β, hβ, hSN⟩
  · exact Or.inl ⟨γ, hγ, hMN,
      native_root_of_proportional_denominator_is_scaled_plane H I E hH e hd hind hGauss cM cN r hr γ hγ hMN hformula,
      native_proportional_denominator_source_power H I E hH e hd hind hGauss cS cM cN r hr hroot γ hγ hMN hformula⟩
  · exact Or.inr ⟨hMN, β, hβ, hSN,
      actual_ruling_root_factorization_constructs_characteristic_direction H I E hH e hd hind hGauss cN r hnumerator
        (native_proportional_power_constructs_ruling_factorization H I E hH e hd hind hGauss
          cS cM cN r hr hroot hm hMN β hβ hSN hformula)⟩

end DimensionFourDependence
