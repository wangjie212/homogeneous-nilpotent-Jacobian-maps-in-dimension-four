import DimensionFourDependence.RationalParameterCoefficientAlgebraicity

/-! # Actual closed Gauss coefficients are algebraic over the Gauss parameter -/

namespace DimensionFourDependence

universe u

variable {K : Type u} [Field K]
  (H : Fin 4 → MvPolynomial (Fin 4) K) (I : ImageRelationWitness H)
  {E L : Type u} [Field E] [Field L]
  [Algebra (closedGaussParameterField H I) E]
  [Algebra.IsAlgebraic (closedGaussParameterField H I) E]
  [Algebra (closedGaussParameterField H I) L] [Algebra E L]
  [IsScalarTower (closedGaussParameterField H I) E L]
  [Algebra K L] [IsScalarTower K (closedGaussParameterField H I) L]

local notation "C₀" => closedGaussParameterField H I
local notation "M₀" => projectiveRatioField (K := K)
  (rationalImageNormal H I.equation) (imageNormalPivot H I)

/-- In any compatible field realization of the actual closed Gauss
cover, its further algebraic coefficient extensions are algebraic over
any field containing the actual Gauss parameter. Neither algebraicity
over the Gauss field nor its passage through the closed cover is assumed. -/
theorem closed_gauss_extended_coefficient_images_isAlgebraic
    (e₀ : RatFunc K ≃ₐ[K] M₀) (J : IntermediateField K L)
    (ht : algebraMap C₀ L (algebraMap M₀ C₀ (e₀ RatFunc.X)) ∈ J) :
    ∀ c : E, IsAlgebraic J (algebraMap E L c) := by
  let : Algebra M₀ E := ((algebraMap C₀ E).comp (algebraMap M₀ C₀)).toAlgebra
  let : IsScalarTower M₀ C₀ E := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let : Algebra.IsAlgebraic M₀ E := Algebra.IsAlgebraic.trans M₀ C₀ E
  let f : M₀ →ₐ[K] L :=
    (IsScalarTower.toAlgHom K C₀ L).comp (IsScalarTower.toAlgHom K M₀ C₀)
  apply rational_parameter_algebraic_coefficient_images e₀ f (algebraMap E L) _ J ht
  ext m
  exact IsScalarTower.algebraMap_apply C₀ E L (algebraMap M₀ C₀ m)

end DimensionFourDependence
