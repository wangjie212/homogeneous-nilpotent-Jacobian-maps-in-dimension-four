import DimensionFourDependence.ExtendedActualGaussRuling
import DimensionFourDependence.RulingFormRelations

/-! # A ruling chosen from the original map supplies its actual binary coordinate data -/

namespace DimensionFourDependence

open MvPolynomial Matrix Module AlgebraicGeometry

universe u

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 2000000
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

/-- A rational Gauss parameter with independent actual normal jets,
chosen from the original nonplanar homogeneous map of Gauss dimension one. -/
noncomputable def actualGaussRulingParameterChoice
    {K : Type u} [Field K] [CharZero K]
    (H : Fin 4 → MvPolynomial (Fin 4) K) (I : ImageRelationWitness H)
    {d : ℕ} (hH : IsHomogMap H d) (hd : 0 < d)
    (hind : ¬ ComponentsDependent H) (hGauss : gaussImageDimension H I = 1) :
    RatFunc K ≃ₐ[K] projectiveRatioField (K := K)
      (rationalImageNormal H I.equation) (imageNormalPivot H I) :=
  Classical.choose (actual_gauss_curve_three_successive_covectors_independent H hd hH hind I hGauss)

/-- The selected original Gauss parameter has the required actual
independent normal jets; this is a derived property of the original map. -/
theorem actualGaussRulingParameterChoice_jet_independent
    {K : Type u} [Field K] [CharZero K]
    (H : Fin 4 → MvPolynomial (Fin 4) K) (I : ImageRelationWitness H)
    {d : ℕ} (hH : IsHomogMap H d) (hd : 0 < d)
    (hind : ¬ ComponentsDependent H) (hGauss : gaussImageDimension H I = 1) :
    LinearIndependent (RatFunc K)
      (rationalParameterJetMatrix (gaussParameterNormal H I
        (actualGaussRulingParameterChoice H I hH hd hind hGauss))).row := by
  obtain ⟨_i, _j, _hminor, hLI⟩ :=
    Classical.choose_spec (actual_gauss_curve_three_successive_covectors_independent H hd hH hind I hGauss)
  exact hLI

variable {K : Type u} [Field K] [CharZero K]
  (H : Fin 4 → MvPolynomial (Fin 4) K) (I : ImageRelationWitness H)
  (E : Type u) [Field E] [Algebra (closedGaussParameterField H I) E]
  [Algebra.IsAlgebraic (closedGaussParameterField H I) E]
  {d : ℕ} (hH : IsHomogMap H d)
  (e : RatFunc K ≃ₐ[K] closedGaussParameterField H I)
  (hd : 0 < d) (hind : ¬ ComponentsDependent H) (hGauss : gaussImageDimension H I = 1)

local notation "N" => extendedClosedGaussNormalizationScheme H I E hH e
local notation "w" => extendedClosedGaussNormalizationHyperplaneWeight H I E hH e

local instance extendedChosenGaussRulingIntegral : IsIntegral N :=
  extendedClosedGaussNormalizationScheme_isIntegral H I E hH e
noncomputable local instance extendedChosenGaussRulingAlgebra : Algebra E (N).functionField :=
  extendedClosedGaussOwnFunctionFieldAlgebra H I E hH e

/-- The actual extended ruling matrix selected from the original map. -/
noncomputable def extendedClosedGaussChosenRulingMatrix : Matrix (Fin 2) (Fin 4) E :=
  extendedClosedGaussRulingMatrix H I E (actualGaussRulingParameterChoice H I hH hd hind hGauss)

local notation "A₀" => extendedClosedGaussChosenRulingMatrix H I E hH hd hind hGauss
local notation "W₀" => LinearMap.ker (A₀).toLin'

omit [Algebra.IsAlgebraic (closedGaussParameterField H I) E] in
/-- The chosen actual extended ruling is two-dimensional without
a supplied kernel dimension or independent covector hypothesis. -/
theorem extendedClosedGaussChosenRulingMatrix_kernel_finrank : finrank E W₀ = 2 :=
  extendedClosedGaussRulingMatrix_kernel_finrank H I E _
    (actualGaussRulingParameterChoice_jet_independent H I hH hd hind hGauss)

/-- Every actual native component value lies in the chosen actual
extended ruling after passing to the native scheme function field. -/
theorem extendedClosedGauss_native_output_mem_chosen_ruling :
    (A₀).map (algebraMap E (N).functionField) *ᵥ
      (fun i => aeval w (MvPolynomial.map (extendedClosedGaussSourceCoefficientHom H I E) (H i))) = 0 :=
  extendedClosedGauss_native_output_mem_actual_ruling H I E hH e hd _

/-- Independent forms on the chosen actual ruling give all
original component-span coefficients, with all ruling and source-point
data constructed from the original map. -/
theorem extendedClosedGauss_native_output_span_of_chosen_ruling_forms
    (cS cN : Fin 4 → E)
    (hpair : LinearIndependent E ![rulingFormRestriction W₀ cS, rulingFormRestriction W₀ cN]) :
    ∃ bS bN : Fin 4 → E, ∀ i,
      aeval w (MvPolynomial.map (extendedClosedGaussSourceCoefficientHom H I E) (H i)) =
        algebraMap E (N).functionField (bS i) * aeval w (extendedClosedGaussOutputLinearPolynomial H I E cS) +
          algebraMap E (N).functionField (bN i) * aeval w (extendedClosedGaussOutputLinearPolynomial H I E cN) :=
  extendedClosedGauss_native_output_span_of_independent_ruling_forms H I E hH e hd _
    (actualGaussRulingParameterChoice_jet_independent H I hH hd hind hGauss) cS cN hpair

/-- A binary relation of the actual ruling-restricted forms gives
the original binary relation of the actual output-linear section values.
Only the ruling relation is an input, not a native field equation. -/
theorem extendedClosedGauss_chosen_ruling_binary_output_relation
    (cS cM cN : Fin 4 → E) (α β : E)
    (hlinear : rulingFormRestriction W₀ cS = α • rulingFormRestriction W₀ cM +
      β • rulingFormRestriction W₀ cN) :
    aeval w (extendedClosedGaussOutputLinearPolynomial H I E cS) =
      algebraMap E (N).functionField α * aeval w (extendedClosedGaussOutputLinearPolynomial H I E cM) +
        algebraMap E (N).functionField β * aeval w (extendedClosedGaussOutputLinearPolynomial H I E cN) := by
  have hv := ruling_form_binary_relation_after_extension (E := (N).functionField)
    (A₀) cS cM cN α β hlinear _
    (extendedClosedGauss_native_output_mem_chosen_ruling H I E hH e hd hind hGauss)
  simp only [dotProduct] at hv
  rw [← extendedClosedGaussOutputLinearPolynomial_value H I E hH e cS,
    ← extendedClosedGaussOutputLinearPolynomial_value H I E hH e cM,
    ← extendedClosedGaussOutputLinearPolynomial_value H I E hH e cN] at hv
  exact hv

end DimensionFourDependence
