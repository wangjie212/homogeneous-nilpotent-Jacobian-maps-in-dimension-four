import DimensionFourDependence.ExtendedGaussSourceMorphism
import DimensionFourDependence.ClosedGaussPencilSchemeCharts
import DimensionFourDependence.ReducedClosureLift

/-! # The coefficient-extended pencil maps to the original Gauss pencil -/

namespace DimensionFourDependence

open MvPolynomial AlgebraicGeometry CategoryTheory Topology

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {K : Type u} [Field K] [CharZero K]
  (H : Fin 4 → MvPolynomial (Fin 4) K) (I : ImageRelationWitness H)
  (E : Type u) [Field E] [Algebra (closedGaussParameterField H I) E]
  [Algebra.IsAlgebraic (closedGaussParameterField H I) E]
  {d : ℕ} (hH : IsHomogMap H d)
  (e : RatFunc K ≃ₐ[K] closedGaussParameterField H I)

local notation "C₀" => closedGaussParameterField H I
local notation "P₀" => AlgebraicGeometry.Proj (homogeneousSubmodule (Fin 4) C₀)
local notation "Q₀" => closedGaussPencilScheme H hH I e
local notation "Qₑ" => extendedClosedGaussPencilScheme H I E hH e
local notation "ι₀" => closedGaussPencilSchemeInclusion H hH I e
local notation "ιₑ" => extendedClosedGaussPencilSchemeInclusion H I E hH e
local notation "cₑ" => polynomialProjectiveCoefficientMap (algebraMap C₀ E)

/-- The actual graded coefficient projection sends the extended
pencil's original generic point to the original pencil generic point. -/
theorem extendedClosedGaussPencilGenericPoint_coefficient_image :
    (cₑ) (extendedClosedGaussPencilGenericPoint H I E hH e) =
      closedGaussPencilProjectiveGenericPoint H hH I e := by
  apply ProjectiveSpectrum.ext
  apply HomogeneousIdeal.toIdeal_injective
  change (extendedClosedGaussPencilIdeal H I E).comap
    (MvPolynomial.map (algebraMap C₀ E)) = _
  exact extendedClosedGaussPencilIdeal_comap H I E

/-- The entire actual extended pencil projects into the original
reduced projective pencil, not merely into ambient projective space. -/
theorem extendedClosedGaussPencil_coefficient_range_subset :
    Set.range ((ιₑ) ≫ (cₑ)) ⊆ closure {closedGaussPencilProjectiveGenericPoint H hH I e} := by
  rintro _ ⟨y, rfl⟩
  have hy : (ιₑ) y ∈ closure {extendedClosedGaussPencilGenericPoint H I E hH e} :=
    (reducedPointClosureInclusion_range
      (AlgebraicGeometry.Proj (homogeneousSubmodule (Fin 4) E))
      (extendedClosedGaussPencilGenericPoint H I E hH e)).le ⟨y, rfl⟩
  have hspec : extendedClosedGaussPencilGenericPoint H I E hH e ⤳ (ιₑ) y :=
    specializes_iff_mem_closure.mpr hy
  have hm := hspec.map (cₑ).continuous
  rw [extendedClosedGaussPencilGenericPoint_coefficient_image H I E hH e] at hm
  exact specializes_iff_mem_closure.mp hm

/-- The coefficient-extended pencil's actual morphism to the original
closed Gauss pencil, constructed through its reduced closed immersion. -/
noncomputable def extendedClosedGaussPencilToOriginal : Qₑ ⟶ Q₀ := by
  let : IsIntegral Qₑ := extendedClosedGaussPencilScheme_isIntegral H I E hH e
  exact reducedPointClosureLift (X := P₀) (Y := Qₑ) (closedGaussPencilProjectiveGenericPoint H hH I e)
    ((ιₑ) ≫ (cₑ)) (extendedClosedGaussPencil_coefficient_range_subset H I E hH e)

/-- The morphism to the original pencil retains the specified
ambient coefficient projection. -/
theorem extendedClosedGaussPencilToOriginal_inclusion :
    extendedClosedGaussPencilToOriginal H I E hH e ≫ (ι₀) = (ιₑ) ≫ (cₑ) := by
  let : IsIntegral Qₑ := extendedClosedGaussPencilScheme_isIntegral H I E hH e
  unfold extendedClosedGaussPencilToOriginal
  exact reducedPointClosureLift_fac _ _ _

/-- Original pencil coordinate opens pull back to precisely the
original coefficient-tensor charts on the extended pencil. -/
theorem extendedClosedGaussPencilToOriginal_preimage_chart
    (s : Fin 4 ≃ Option (Fin 3)) :
    extendedClosedGaussPencilToOriginal H I E hH e ⁻¹ᵁ
        closedGaussPencilSchemeChartOpen H hH I e (s.symm none) =
      extendedClosedGaussPencilChartOpen H I E hH e s := by
  unfold closedGaussPencilSchemeChartOpen
  rw [← Scheme.Hom.comp_preimage, extendedClosedGaussPencilToOriginal_inclusion,
    Scheme.Hom.comp_preimage, polynomialProjectiveCoefficientMap_preimage_basicOpen]
  rfl

end DimensionFourDependence
