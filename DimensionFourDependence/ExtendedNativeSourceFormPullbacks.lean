import DimensionFourDependence.ProjectiveChartPolynomialCoefficientChange
import DimensionFourDependence.ExtendedSourceFormLocalIdeals
import DimensionFourDependence.ProjectiveSectionOrderMultiplicity

/-! # Native original source-form coefficients are the actual original-source pullbacks -/

namespace DimensionFourDependence

open MvPolynomial AlgebraicGeometry CategoryTheory

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 2000000
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

variable {K : Type u} [Field K] [CharZero K]
  (H : Fin 4 → MvPolynomial (Fin 4) K) (I : ImageRelationWitness H)
  (E : Type u) [Field E] [Algebra (closedGaussParameterField H I) E]
  [Algebra.IsAlgebraic (closedGaussParameterField H I) E]
  {d : ℕ} (hH : IsHomogMap H d)
  (e : RatFunc K ≃ₐ[K] closedGaussParameterField H I)

local notation "N" => extendedClosedGaussNormalizationScheme H I E hH e
local notation "V" a:max => extendedClosedGaussNormalizationChartOpen H I E hH e (finSuccEquiv' a)
local notation "f" => extendedClosedGaussNormalizationProjectiveMap H I E hH e
local notation "m" => extendedClosedGaussNormalizationSourceMorphism H I E hH e
local notation "φ" => extendedClosedGaussSourceCoefficientHom H I E
local notation "g" => polynomialProjectiveCoefficientMap φ
local notation "U₀" a:max => Proj.basicOpen (homogeneousSubmodule (Fin 4) K) (X a)
local notation "U₁" a:max => Proj.basicOpen (homogeneousSubmodule (Fin 4) E) (X a)

local instance extendedNativeSourceFormPullbacksIntegral : IsIntegral N :=
  extendedClosedGaussNormalizationScheme_isIntegral H I E hH e

/-- In the original coordinate indexing, the actual source
projection has exactly the actual native original chart as inverse open. -/
theorem extendedClosedGaussNormalizationSourceMorphism_preimage_original (a : Fin 4) :
    (m) ⁻¹ᵁ U₀ a = V a := by
  simpa only [finSuccEquiv'_symm_none] using
    extendedClosedGaussNormalizationSourceMorphism_preimage_basicOpen H I E hH e (finSuccEquiv' a)

/-- Every actual native chart point maps into the same original
source-coordinate open. -/
theorem extendedClosedGaussNormalizationSourceMorphism_mem_original
    (z : N) (a : Fin 4) (ha : z ∈ V a) : (m) z ∈ U₀ a := by
  change z ∈ (m) ⁻¹ᵁ U₀ a
  rwa [extendedClosedGaussNormalizationSourceMorphism_preimage_original]

/-- The entire actual regular native source-polynomial coefficient
equals the actual original-source chart-section pullback. -/
theorem extendedClosedGaussChartPolynomialCoefficient_eq_source_appLE
    (P : MvPolynomial (Fin 4) K) (a : Fin 4) :
    extendedClosedGaussChartPolynomialCoefficient H I E hH e (MvPolynomial.map φ P) a =
      (m).appLE (U₀ a) (V a)
        (le_of_eq (extendedClosedGaussNormalizationSourceMorphism_preimage_original H I E hH e a).symm)
        (projectiveChartPolynomialSectionHom K a P) := by
  let hf := le_of_eq (extendedClosedGaussNormalizationProjectiveMap_preimage H I E hH e a).symm
  let hg := le_of_eq (polynomialProjectiveCoefficientMap_preimage_basicOpen φ a).symm
  have hcomp := Scheme.Hom.appLE_comp_appLE f g (U₀ a) (U₁ a) (V a) hg hf
  have heq : (f) ≫ g = m := by
    unfold extendedClosedGaussNormalizationProjectiveMap extendedClosedGaussNormalizationSourceMorphism
      extendedClosedGaussPencilSourceMorphism
    exact Category.assoc _ _ _
  calc
    _ = (f).appLE (U₁ a) (V a) hf
        (projectiveChartPolynomialSectionHom E a (MvPolynomial.map φ P)) := by
      unfold extendedClosedGaussChartPolynomialCoefficient
      rw [projectivePullbackChartPolynomialHom_eq_app]
      rfl
    _ = (f).appLE (U₁ a) (V a) hf
        ((g).appLE (U₀ a) (U₁ a) hg (projectiveChartPolynomialSectionHom K a P)) :=
      congrArg (fun v => (f).appLE (U₁ a) (V a) hf v)
        (polynomialProjectiveCoefficientMap_chartPolynomialSection φ a P).symm
    _ = _ := by
      have h := ConcreteCategory.congr_hom hcomp (projectiveChartPolynomialSectionHom K a P)
      simpa only [heq, ConcreteCategory.comp_apply] using h

/-- The native local coefficient of every original source
polynomial equals its actual geometric original-source stalk pullback. -/
theorem extendedClosedGaussPolynomialCoefficientGerm_eq_source_stalkMap
    (P : MvPolynomial (Fin 4) K) (z : N) (a : Fin 4) (ha : z ∈ V a) :
    extendedClosedGaussPolynomialCoefficientGerm H I E hH e (MvPolynomial.map φ P) z a ha =
      (m).stalkMap z
        ((AlgebraicGeometry.Proj (homogeneousSubmodule (Fin 4) K)).presheaf.germ
          (U₀ a) ((m) z) (extendedClosedGaussNormalizationSourceMorphism_mem_original H I E hH e z a ha)
          (projectiveChartPolynomialSectionHom K a P)) := by
  rw [Scheme.Hom.germ_stalkMap_apply]
  unfold extendedClosedGaussPolynomialCoefficientGerm
  rw [extendedClosedGaussChartPolynomialCoefficient_eq_source_appLE]
  unfold Scheme.Hom.appLE
  simp only [ConcreteCategory.comp_apply]
  exact (N).presheaf.germ_res_apply _ z ha _

/-- The original section in Lemma 4.2's standard frame has exactly
the native coefficient germ used by the product-power argument. -/
theorem extendedClosedGaussPolynomialCoefficientGerm_eq_original_source_section
    (P : MvPolynomial (Fin 4) K) (z : N) (a : Fin 4) (ha : z ∈ V a) :
    extendedClosedGaussPolynomialCoefficientGerm H I E hH e (MvPolynomial.map φ P) z a ha =
      (m).stalkMap z
        ((AlgebraicGeometry.Proj (homogeneousSubmodule (Fin 4) K)).presheaf.germ
          (U₀ a) ((m) z) (extendedClosedGaussNormalizationSourceMorphism_mem_original H I E hH e z a ha)
          ((originalProjectiveAffineSectionEquiv (K := K) a).symm
            (projectiveSourceSectionHom (finSuccEquiv' a) P))) := by
  have hsection : (originalProjectiveAffineSectionEquiv (K := K) a).symm
      (projectiveSourceSectionHom (finSuccEquiv' a) P) = projectiveChartPolynomialSectionHom K a P := by
    simpa +instances only [finSuccEquiv'_symm_none] using
      originalProjectiveAffineSectionEquiv_symm_sourceSection K (finSuccEquiv' a) P
  rw [hsection]
  exact extendedClosedGaussPolynomialCoefficientGerm_eq_source_stalkMap H I E hH e P z a ha

/-- Native regular local orders of all original component forms
supply the actual geometric source-section orders required by Lemma 4.2. -/
theorem actual_native_component_germ_orders_supply_source_section_orders
    (z : N) (a : Fin 4) (ha : z ∈ V a) (b : ℕ)
    (horder : ∀ i, extendedClosedGaussPolynomialCoefficientGerm H I E hH e
      (MvPolynomial.map φ (H i)) z a ha ∈ IsLocalRing.maximalIdeal ((N).presheaf.stalk z) ^ b) :
    ProjectiveSourceSectionOrders m z H b := by
  refine ⟨finSuccEquiv' a, ?_, ?_⟩
  · simpa only [finSuccEquiv'_symm_none] using
      extendedClosedGaussNormalizationSourceMorphism_mem_original H I E hH e z a ha
  · intro i
    have hi := horder i
    rw [extendedClosedGaussPolynomialCoefficientGerm_eq_original_source_section H I E hH e (H i) z a ha] at hi
    simpa +instances only [finSuccEquiv'_symm_none] using hi

end DimensionFourDependence
