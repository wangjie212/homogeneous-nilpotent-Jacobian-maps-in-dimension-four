import DimensionFourDependence.ProjectiveCoefficientEvaluation
import DimensionFourDependence.ExtendedGaussPencilOriginalMap

/-! # Original-pencil coefficients and sections have canonical tensor values -/

namespace DimensionFourDependence

open MvPolynomial AlgebraicGeometry CategoryTheory
open scoped TensorProduct

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

variable {K : Type u} [Field K] [CharZero K]
  (H : Fin 4 → MvPolynomial (Fin 4) K) (I : ImageRelationWitness H)
  (E : Type u) [Field E] [Algebra (closedGaussParameterField H I) E]
  [Algebra.IsAlgebraic (closedGaussParameterField H I) E]
  {d : ℕ} (hH : IsHomogMap H d)
  (e : RatFunc K ≃ₐ[K] closedGaussParameterField H I)
  (s : Fin 4 ≃ Option (Fin 3))

local notation "C₀" => closedGaussParameterField H I
local notation "x₀" => rationalCoordinate (K := K) (n := 4)
local notation "zₑ" => primeQuotientCoordinate (extendedClosedGaussPencilIdeal H I E)
local notation "S₀" => projectiveCoordinateChartAlgebra (C := C₀) x₀ (s.symm none)
local notation "Sₑ" => projectiveCoordinateChartAlgebra (C := E) zₑ (s.symm none)
local notation "U₀" => Proj.basicOpen (homogeneousSubmodule (Fin 4) C₀) (X (s.symm none))
local notation "Uₑ" => Proj.basicOpen (homogeneousSubmodule (Fin 4) E) (X (s.symm none))
local notation "σ" => polynomialProjectiveCoefficientMap (algebraMap C₀ E)
local notation "hU" => le_of_eq (Eq.symm (polynomialProjectiveCoefficientMap_preimage_basicOpen
  (algebraMap C₀ E) (s.symm none)))

/-- The original pencil-chart map to the extended ratio chart is the
specified tensor inclusion through its checked coordinate isomorphism. -/
noncomputable def extendedClosedGaussPencilChartCoefficientHom : S₀ →+* Sₑ :=
  (extendedClosedGaussRatioCoordinateEquiv H I E hH e s).toRingHom.comp
    (Algebra.TensorProduct.includeLeft : S₀ →ₐ[C₀] S₀ ⊗[C₀] E).toRingHom

/-- Every original pencil ratio has its original extended value. -/
theorem extendedClosedGaussPencilChartCoefficientHom_ratio (i : Fin 4) :
    extendedClosedGaussPencilChartCoefficientHom H I E hH e s
      (projectiveChartTransition (C := C₀) x₀ (s.symm none) i) =
        projectiveChartTransition (C := E) zₑ (s.symm none) i :=
  extendedClosedGaussRatioCoordinateEquiv_tmul_ratio H I E hH e s i

/-- The actual full Gauss coefficient field, not only the original
constant field, maps to its specified extended coefficients. -/
theorem extendedClosedGaussPencilChartCoefficientHom_coefficient (c : C₀) :
    extendedClosedGaussPencilChartCoefficientHom H I E hH e s (algebraMap C₀ S₀ c) =
      algebraMap E Sₑ (algebraMap C₀ E c) := by
  change extendedClosedGaussRatioCoordinateEquiv H I E hH e s
    ((algebraMap C₀ S₀ c) ⊗ₜ[C₀] (1 : E)) = _
  have ht : (algebraMap C₀ S₀ c) ⊗ₜ[C₀] (1 : E) = (1 : S₀) ⊗ₜ[C₀] algebraMap C₀ E c := by
    simp only [Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul, TensorProduct.tmul_smul]
  rw [ht]
  exact extendedClosedGaussRatioCoordinateEquiv_tmul_coefficient H I E hH e s _

/-- Coefficient pullback on the actual ambient projective sections
agrees with the full original pencil-chart tensor inclusion. -/
theorem extendedClosedGaussPencilProjectiveSection_coefficient_compatibility
    (r : Γ(AlgebraicGeometry.Proj (homogeneousSubmodule (Fin 4) C₀), U₀)) :
    projectiveAmbientSectionToSource (C := E) zₑ (s.symm none)
        (extendedClosedGaussRatioCoordinate_ne_zero H I E _) ((σ).appLE U₀ Uₑ hU r) =
      extendedClosedGaussPencilChartCoefficientHom H I E hH e s
        (projectiveAmbientSectionToSource (C := C₀) x₀ (s.symm none)
          (source_rationalCoordinate_ne_zero _) r) := by
  exact projective_ambient_coefficient_section_compatibility (algebraMap C₀ E)
    x₀ zₑ (s.symm none) (extendedClosedGaussPencilChartCoefficientHom H I E hH e s)
    (extendedClosedGaussPencilChartCoefficientHom_coefficient H I E hH e s)
    (extendedClosedGaussPencilChartCoefficientHom_ratio H I E hH e s)
    (source_rationalCoordinate_ne_zero _) (extendedClosedGaussRatioCoordinate_ne_zero H I E _) r

/-- Original ambient projective sections in the tensor order of the
actual extended-pencil chart. -/
noncomputable def extendedClosedGaussPencilAmbientTensorSectionHom :
    Γ(AlgebraicGeometry.Proj (homogeneousSubmodule (Fin 4) C₀), U₀) →+* S₀ ⊗[C₀] E :=
  (Algebra.TensorProduct.includeLeft : S₀ →ₐ[C₀] S₀ ⊗[C₀] E).toRingHom.comp
    (projectiveAmbientSectionToSource (C := C₀) x₀ (s.symm none)
      (source_rationalCoordinate_ne_zero _))

/-- The tensor section homomorphism preserves the actual geometric
coefficient pullback on every ambient projective section. -/
theorem extendedClosedGaussPencilAmbientTensorSectionHom_compatibility
    (r : Γ(AlgebraicGeometry.Proj (homogeneousSubmodule (Fin 4) C₀), U₀)) :
    extendedClosedGaussRatioCoordinateEquiv H I E hH e s
        (extendedClosedGaussPencilAmbientTensorSectionHom H I E s r) =
      projectiveAmbientSectionToSource (C := E) zₑ (s.symm none)
        (extendedClosedGaussRatioCoordinate_ne_zero H I E _) ((σ).appLE U₀ Uₑ hU r) :=
  (extendedClosedGaussPencilProjectiveSection_coefficient_compatibility H I E hH e s r).symm

end DimensionFourDependence
