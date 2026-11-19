import DimensionFourDependence.ExtendedSourceFormLocalIdeals

/-! # The specified extended Gauss constants act on the actual native source stalk -/

namespace DimensionFourDependence

open MvPolynomial AlgebraicGeometry

universe u

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000

variable {K : Type u} [Field K] [CharZero K]
  (H : Fin 4 → MvPolynomial (Fin 4) K) (I : ImageRelationWitness H)
  (E : Type u) [Field E] [Algebra (closedGaussParameterField H I) E]
  [Algebra.IsAlgebraic (closedGaussParameterField H I) E]
  {d : ℕ} (hH : IsHomogMap H d)
  (e : RatFunc K ≃ₐ[K] closedGaussParameterField H I)

local notation "N" => extendedClosedGaussNormalizationScheme H I E hH e

local instance nativePencilStalkConstantsIntegral : IsIntegral N :=
  extendedClosedGaussNormalizationScheme_isIntegral H I E hH e
noncomputable local instance nativePencilStalkConstantsFieldAlgebra : Algebra E (N).functionField :=
  extendedClosedGaussOwnFunctionFieldAlgebra H I E hH e

/-- The actual global coefficient functions give the actual local
coefficient action, without choosing an unrelated copy of E. -/
@[instance_reducible]
noncomputable def extendedClosedGaussStalkCoefficientAlgebra (z : N) :
    Algebra E ((N).presheaf.stalk z) :=
  (((N).presheaf.germ ⊤ z (by trivial)).hom.comp
    (extendedClosedGaussGlobalConstantHom H I E hH e)).toAlgebra

/-- The local coefficient action agrees with the specified native
function-field action on every original extended coefficient. -/
theorem extendedClosedGaussStalkCoefficientAlgebra_scalarTower (z : N) :
    letI := extendedClosedGaussStalkCoefficientAlgebra H I E hH e z
    IsScalarTower E ((N).presheaf.stalk z) (N).functionField := by
  letI := extendedClosedGaussStalkCoefficientAlgebra H I E hH e z
  exact IsScalarTower.of_algebraMap_eq (fun c =>
    (extendedClosedGaussGlobalConstantHom_germ_value H I E hH e c z).symm)

end DimensionFourDependence
