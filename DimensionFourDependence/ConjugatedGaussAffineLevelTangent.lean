import DimensionFourDependence.ActualAffineLevelTangent
import DimensionFourDependence.RelativeClosureCoordinateTransport
import DimensionFourDependence.ProjectiveSourceCoordinates

/-! # Global affine tangency for the actual transported Gauss parameter

The actual original source automorphism transports relative closedness of
the closed Gauss field. Its given affine chart value has independent chart
coordinates. Consequently any algebraic-parameter affine triangular field
tangent at the actual source point annihilates the entire original affine
polynomial after extending its coefficients. No new integrality, exact
relation-ideal or relatively-closed-parameter hypothesis is supplied.
-/

namespace DimensionFourDependence

open MvPolynomial

set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 100000

variable {K : Type*} [Field K] [CharZero K]

local notation "S₀" => FractionRing (MvPolynomial (Fin 4) K)
local notation "x₀" => closedGaussPencilChartPoint (K := K) (finSuccEquiv' (1 : Fin 4))

attribute [-instance] IntermediateField.instSMulSubtypeMem in
/-- The actual transported closed Gauss parameter constructs global
annihilation by every algebraic-parameter affine triangular field tangent
at the actual source chart point. All primitive-parameter and source-chart
conditions needed for the argument are derived from the original data. -/
theorem actual_conjugate_gauss_affine_level_tangent_forces_global_annihilation
    (H : Fin 4 → MvPolynomial (Fin 4) K) (I : ImageRelationWitness H)
    (e : RatFunc K ≃ₐ[K] closedGaussParameterField H I) (f : S₀ ≃ₐ[K] S₀)
    (t : S₀) (ht : t = f (closedGaussParameterSourceHom H I e RatFunc.X))
    (P : MvPolynomial (Fin 3) K) (hchart : t = aeval x₀ P)
    (i : Fin 3) (hpartial : pderiv i P ≠ 0)
    (E M : Type*) [Field E] [Field M]
    [Algebra (IntermediateField.adjoin K {t}) E]
    [Algebra.IsAlgebraic (IntermediateField.adjoin K {t}) E]
    [Algebra (IntermediateField.adjoin K {t}) M] [Algebra S₀ M]
    [IsScalarTower (IntermediateField.adjoin K {t}) S₀ M]
    [Algebra E M] [IsScalarTower (IntermediateField.adjoin K {t}) E M]
    (u : Fin 2 → E) (b : Fin 3 → E)
    (htangent : aeval (fun j => algebraMap S₀ M (x₀ j))
      (affineProjectedTangentAction u b
        (MvPolynomial.map ((algebraMap (IntermediateField.adjoin K {t}) E).comp
          (algebraMap K (IntermediateField.adjoin K {t}))) P)) = 0) :
    affineProjectedTangentAction u b
      (MvPolynomial.map ((algebraMap (IntermediateField.adjoin K {t}) E).comp
        (algebraMap K (IntermediateField.adjoin K {t}))) P) = 0 := by
  have hclosed₀ := actual_conjugated_closed_gauss_parameter_field_relatively_closed H I e f
  have hclosed : algebraicClosure (IntermediateField.adjoin K {t}) S₀ = ⊥ :=
    Eq.mpr (congrArg (fun r : S₀ => algebraicClosure (IntermediateField.adjoin K {r}) S₀ = ⊥) ht) hclosed₀
  have htrans : Transcendental K t := by
    intro halg
    have halg' : IsAlgebraic K (f (closedGaussParameterSourceHom H I e RatFunc.X)) := ht ▸ halg
    exact closedGaussParameterSourceHom_X_transcendental H I e
      ((isAlgebraic_algHom_iff f.toAlgHom f.injective).mp halg')
  have hx : AlgebraicIndependent K x₀ := algebraicIndependent_iff_injective_aeval.mpr
    (projective_source_chart_evaluation_injective _)
  exact actual_affine_level_tangent_forces_global_annihilation t htrans x₀ hx P hchart hclosed
    i hpartial E M u b htangent

end DimensionFourDependence
