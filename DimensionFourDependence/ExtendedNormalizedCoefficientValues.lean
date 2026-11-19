import DimensionFourDependence.ExtendedNormalizedAmbientValues
import DimensionFourDependence.ProjectiveConstantSections

/-! # All original tensor charts share the actual coefficient action on the scheme field -/

namespace DimensionFourDependence

open MvPolynomial AlgebraicGeometry CategoryTheory
open scoped TensorProduct

attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] Algebra.TensorProduct.rightAlgebra

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

local notation "C₀" => closedGaussParameterField H I
local notation "N" => extendedClosedGaussNormalizationScheme H I E hH e
local notation "f" => extendedClosedGaussNormalizationProjectiveMap H I E hH e

local instance extendedNormalizedCoefficientValuesIntegral : IsIntegral N := extendedClosedGaussNormalizationScheme_isIntegral H I E hH e

/-- The one actual extended-coefficient map into the normalized
pencil's own function field, given by the original generic stalk morphism. -/
noncomputable def extendedClosedGaussOwnFunctionFieldScalarHom : E →+* (N).functionField :=
  projectivePullbackScalarHom E N f

/-- The actual extended coefficient-field action on the normalized
pencil function field. -/
@[instance_reducible] noncomputable def extendedClosedGaussOwnFunctionFieldAlgebra :
    Algebra E (N).functionField :=
  (extendedClosedGaussOwnFunctionFieldScalarHom H I E hH e).toAlgebra

variable (s : Fin 4 ≃ Option (Fin 3))

local notation "S₀" => projectiveCoordinateChartAlgebra (C := C₀)
  (rationalCoordinate (K := K) (n := 4)) (s.symm none)
local notation "T₀" => S₀ ⊗[C₀] E
local notation "Uₙ" => extendedClosedGaussNormalizationChartOpen H I E hH e s
local notation "Uₑ" => Proj.basicOpen (homogeneousSubmodule (Fin 4) E) (X (s.symm none))

local instance extendedNormalizedCoefficientValuesDomain : IsDomain T₀ := original_tensor_pencil_chart_isDomain H I E s
local instance extendedNormalizedCoefficientValuesNonempty : Nonempty Uₙ := extendedClosedGaussNormalizationChartOpen_nonempty H I E hH e s

/-- The original actual ambient constant section is the original
right tensor coefficient under the actual pencil section map. -/
theorem extendedClosedGaussPencilAmbientSectionHom_constant (c : E) :
    extendedClosedGaussPencilAmbientSectionHom H I E hH e s
        (projectiveConstantSectionHom E Uₑ c) = (1 : S₀) ⊗ₜ[C₀] c := by
  let b := extendedClosedGaussRatioCoordinateEquiv H I E hH e s
  apply b.injective
  change b (b.symm _) = b ((1 : S₀) ⊗ₜ[C₀] c)
  rw [b.apply_symm_apply, projectiveConstantSectionHom_source_value]
  exact (extendedClosedGaussRatioCoordinateEquiv_tmul_coefficient H I E hH e s c).symm

/-- Every original tensor chart's own-function-field embedding has
the same actual extended coefficient map. -/
theorem extendedClosedGaussTensorChartToOwnFunctionField_coefficient (c : E) :
    extendedClosedGaussTensorChartToOwnFunctionField H I E hH e s
        ((1 : S₀) ⊗ₜ[C₀] c) = extendedClosedGaussOwnFunctionFieldScalarHom H I E hH e c := by
  let r := projectiveConstantSectionHom E Uₑ c
  have hval := extendedClosedGaussTensorChartToOwnFunctionField_ambient_section H I E hH e s r
  have hc := extendedClosedGaussPencilAmbientSectionHom_constant H I E hH e s c
  let : Nonempty ((f) ⁻¹ᵁ Uₑ) :=
    extendedClosedGaussNormalizationProjectiveMap_chart_nonempty H I E hH e (s.symm none)
  have hgen := projectivePullbackScalarHom_chart E N f Uₑ c
  exact (congrArg (extendedClosedGaussTensorChartToOwnFunctionField H I E hH e s) hc.symm).trans
    (hval.trans ((congrArg (fun q : Γ(N, Uₙ) => (N).germToFunctionField Uₙ q)
      (extendedClosedGaussNormalizedAmbientChartPullback_eq_app H I E hH e s r)).trans hgen.symm))

/-- The original chart embedding is injective in the actual scheme
function field. -/
theorem extendedClosedGaussTensorChartToOwnFunctionField_injective :
    Function.Injective (extendedClosedGaussTensorChartToOwnFunctionField H I E hH e s) :=
  (extendedClosedGaussNormalizedChartFunctionFieldEquiv H I E hH e s).injective.comp
    (IsFractionRing.injective T₀ (FractionRing T₀))

/-- The original tensor embedding is an algebra homomorphism for
the single actual coefficient action, independently of the original chart. -/
noncomputable def extendedClosedGaussTensorChartToOwnFunctionFieldAlgHom :
    let : Algebra E (N).functionField := extendedClosedGaussOwnFunctionFieldAlgebra H I E hH e
    T₀ →ₐ[E] (N).functionField := by
  let : Algebra E (N).functionField := extendedClosedGaussOwnFunctionFieldAlgebra H I E hH e
  exact { extendedClosedGaussTensorChartToOwnFunctionField H I E hH e s with
    commutes' := extendedClosedGaussTensorChartToOwnFunctionField_coefficient H I E hH e s }

end DimensionFourDependence
