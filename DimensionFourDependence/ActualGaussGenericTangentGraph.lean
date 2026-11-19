import DimensionFourDependence.ConjugatedGaussAffineLevelTangent
import DimensionFourDependence.AffineTangentCoefficientDescent
import DimensionFourDependence.ActualPrimitiveAffineParameter

/-! # A generic tangent with independent coefficients constructs the actual graph

The actual closed Gauss parameter gives geometric integrality and global
annihilation from tangency at its source-chart point. Linear coefficient
functionals construct two normalized original-field tangent lifts from
one such generic tangent with independent horizontal coefficients. Their
quadratic invariant and the actual primitive-parameter degree argument
then construct the entire original affine graph parameter.
-/

namespace DimensionFourDependence

open MvPolynomial

set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 100000

variable {K : Type*} [Field K] [CharZero K]

local notation "S₀" => FractionRing (MvPolynomial (Fin 4) K)
local notation "x₀" => closedGaussPencilChartPoint (K := K) (finSuccEquiv' (1 : Fin 4))

attribute [-instance] IntermediateField.instSMulSubtypeMem in
/-- A single actual algebraic-parameter tangent with independent horizontal
coefficients constructs the complete original quadratic graph parameter.
Global annihilation, two constant normalized lifts, a quadratic potential
and the nonzero affine outer slope are all derived from the actual data. -/
theorem actual_conjugate_gauss_generic_tangent_constructs_original_quadratic_graph_parameter
    (H : Fin 4 → MvPolynomial (Fin 4) K) (I : ImageRelationWitness H)
    (e : RatFunc K ≃ₐ[K] closedGaussParameterField H I) (f : S₀ ≃ₐ[K] S₀)
    (t : S₀) (ht : t = f (closedGaussParameterSourceHom H I e RatFunc.X))
    (P : MvPolynomial (Fin 3) K) (hchart : t = aeval x₀ P)
    (hPw : pderiv (2 : Fin 3) P ≠ 0)
    (E M : Type*) [Field E] [Field M]
    [Algebra (IntermediateField.adjoin K {t}) E] [Algebra K E]
    [IsScalarTower K (IntermediateField.adjoin K {t}) E]
    [Algebra.IsAlgebraic (IntermediateField.adjoin K {t}) E]
    [Algebra (IntermediateField.adjoin K {t}) M] [Algebra S₀ M]
    [IsScalarTower (IntermediateField.adjoin K {t}) S₀ M]
    [Algebra E M] [IsScalarTower (IntermediateField.adjoin K {t}) E M]
    (u : Fin 2 → E) (hu : LinearIndependent K u) (b : Fin 3 → E)
    (htangent : aeval (fun j => algebraMap S₀ M (x₀ j))
      (affineProjectedTangentAction u b (MvPolynomial.map (algebraMap K E) P)) = 0) :
    ∃ Q : MvPolynomial (Fin 2) K, Q.totalDegree ≤ 2 ∧
      ∃ a b : K, a ≠ 0 ∧ P = C a * (X 2 - rename Fin.castSucc Q) + C b := by
  have hcomp : (algebraMap (IntermediateField.adjoin K {t}) E).comp
      (algebraMap K (IntermediateField.adjoin K {t})) = algebraMap K E :=
    (IsScalarTower.algebraMap_eq K (IntermediateField.adjoin K {t}) E).symm
  have hglobal : affineProjectedTangentAction u b (MvPolynomial.map (algebraMap K E) P) = 0 := by
    have h := actual_conjugate_gauss_affine_level_tangent_forces_global_annihilation
      H I e f t ht P hchart (2 : Fin 3) hPw E M u b (by simpa only [hcomp] using htangent)
    simpa only [hcomp] using h
  obtain ⟨b₀, b₁, hx, hz⟩ :=
    independent_horizontal_coefficient_tangent_constructs_original_normalized_lifts P u hu b hglobal
  obtain ⟨Q, F, hQ, hF, hPF⟩ :=
    invariant_affine_tangent_lifts_construct_quadratic_composite_parameter P hPw b₀ b₁ hx hz
  obtain ⟨_hdegree, a, c, ha, hshape⟩ :=
    actual_conjugate_gauss_affine_composite_parameter_constructs_affine_graph
      H I e f t ht P hchart Q F hF hPF
  exact ⟨Q, hQ, a, c, ha, hshape⟩

end DimensionFourDependence
