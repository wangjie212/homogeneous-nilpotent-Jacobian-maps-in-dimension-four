import DimensionFourDependence.ExtendedNativeNormalizedSections
import DimensionFourDependence.ProjectiveSectionProjectionRegularity

/-! # The native global hyperplane section supplies both norm regularities -/

namespace DimensionFourDependence

open AlgebraicGeometry

universe u
set_option synthInstance.maxHeartbeats 110000
set_option maxHeartbeats 2600000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

variable {K : Type u} [Field K] [CharZero K]
  (H : Fin 4 → MvPolynomial (Fin 4) K) (I : ImageRelationWitness H)
  (E : Type u) [Field E] [Algebra (closedGaussParameterField H I) E]
  [Algebra.IsAlgebraic (closedGaussParameterField H I) E]
  {d : ℕ} (hH : IsHomogMap H d)
  (e : RatFunc K ≃ₐ[K] closedGaussParameterField H I)

local notation "N" => extendedClosedGaussNormalizationScheme H I E hH e
local notation "M" => extendedClosedGaussNormalizationHyperplaneModuleSheaf H I E hH e
local notation "w" => extendedClosedGaussNormalizationHyperplaneWeight H I E hH e

local instance nativeNormRegularityIntegral : IsIntegral N :=
  extendedClosedGaussNormalizationScheme_isIntegral H I E hH e
noncomputable local instance nativeNormRegularityAlgebra : Algebra E (N).functionField :=
  extendedClosedGaussOwnFunctionFieldAlgebra H I E hH e

/-- A monic projection of the actual normalized pencil and its actual
global hyperplane section give integral coefficients at both projection
frames. These are the two hypotheses of the norm-degree estimate. -/
theorem actual_native_pencil_global_section_both_norm_regularities
    (s : Γ(M, ⊤)) (a : Fin 4 ≃ Option (Fin 3))
    (hbase : w (a.symm none) ≠ 0) (T : (Fin 3 → E) ≃ₗ[E] (Fin 3 → E))
    {k : Type u} [Field k] [Algebra E k]
    [Algebra (RatFunc k) (N).functionField] [IsScalarTower E (RatFunc k) (N).functionField]
    [Algebra (Polynomial k) (N).functionField] [IsScalarTower (Polynomial k) (RatFunc k) (N).functionField]
    [Algebra (rationalInfinityRing k) (N).functionField]
    [IsScalarTower (rationalInfinityRing k) (RatFunc k) (N).functionField]
    (v : (N).functionField) (u₀ : k)
    (hcoords : linearProjectionCoordinate T (fun j => w (a.symm (some j)) / w (a.symm none)) =
      ![v, algebraMap (RatFunc k) (N).functionField RatFunc.X,
        algebraMap (RatFunc k) (N).functionField (RatFunc.C u₀)])
    (P : Polynomial (Polynomial k)) (hP : P.Monic)
    (hdegree : ∀ i ≤ P.natDegree, (P.coeff i).natDegree + i ≤ P.natDegree)
    (hroot : Polynomial.aeval v P = 0) :
    let r := extendedClosedGaussHyperplaneOwnCoefficient H I E hH e s (a.symm none)
    IsIntegral (Polynomial k) r ∧ IsIntegral (rationalInfinityRing k)
      (algebraMap (RatFunc k) (N).functionField (RatFunc.X⁻¹) * r) :=
  projective_original_chart_section_two_projection_regularities w
    (extendedClosedGaussHyperplaneProjectiveNormalizedSection H I E hH e s)
    a hbase T v u₀ hcoords P hP hdegree hroot

end DimensionFourDependence
