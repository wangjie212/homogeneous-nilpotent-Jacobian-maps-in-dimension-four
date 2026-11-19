import DimensionFourDependence.RelativeClosureCoordinateTransport
import DimensionFourDependence.PrimitivePolynomialParameterDegree
import DimensionFourDependence.IndependentAffineTangentParameter
import DimensionFourDependence.LinearMonicProjectionChoice

/-! # The actual primitive affine cone parameter has a linear outer polynomial

Relative algebraic closedness is retained through the original source
conjugacy. Applying it to the entire constructed quadratic composite
parameter forces its outer polynomial to have degree one and constructs
its nonzero affine slope. No new primitive-parameter premise is supplied.
-/

namespace DimensionFourDependence

open MvPolynomial Matrix

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 100000

variable {K : Type*} [Field K]

local notation "S₀" => FractionRing (MvPolynomial (Fin 4) K)
local notation "x₀" => closedGaussPencilChartPoint (K := K) (finSuccEquiv' (1 : Fin 4))

/-- The exact actual transported closed Gauss parameter forces the
outer polynomial in every complete affine graph composite to be linear,
and constructs its original nonzero slope and intercept. -/
theorem actual_conjugate_gauss_affine_composite_parameter_constructs_affine_graph
    (H : Fin 4 → MvPolynomial (Fin 4) K) (I : ImageRelationWitness H)
    (e : RatFunc K ≃ₐ[K] closedGaussParameterField H I) (f : S₀ ≃ₐ[K] S₀)
    (t : S₀) (ht : t = f (closedGaussParameterSourceHom H I e RatFunc.X))
    (P : MvPolynomial (Fin 3) K) (hchart : t = aeval x₀ P)
    (Q : MvPolynomial (Fin 2) K) (F : Polynomial K) (hF : 0 < F.natDegree)
    (hcomp : P = Polynomial.aeval (X 2 - rename Fin.castSucc Q) F) :
    F.natDegree = 1 ∧ ∃ a b : K, a ≠ 0 ∧ P = C a * (X 2 - rename Fin.castSucc Q) + C b := by
  have hclosed₀ := actual_conjugated_closed_gauss_parameter_field_relatively_closed H I e f
  have hclosed : algebraicClosure (IntermediateField.adjoin K {t}) S₀ = ⊥ :=
    Eq.mpr (congrArg (fun r : S₀ => algebraicClosure (IntermediateField.adjoin K {r}) S₀ = ⊥) ht) hclosed₀
  have htrans : Transcendental K t := by
    intro halg
    have halg' : IsAlgebraic K (f (closedGaussParameterSourceHom H I e RatFunc.X)) := ht ▸ halg
    exact closedGaussParameterSourceHom_X_transcendental H I e
      ((isAlgebraic_algHom_iff f.toAlgHom f.injective).mp halg')
  have hvalue : t = Polynomial.aeval (aeval x₀ (X 2 - rename Fin.castSucc Q)) F := by
    calc
      t = aeval x₀ P := hchart
      _ = aeval x₀ (Polynomial.aeval (X 2 - rename Fin.castSucc Q) F) := congrArg (aeval x₀) hcomp
      _ = _ := (Polynomial.aeval_algHom_apply (aeval x₀) (X 2 - rename Fin.castSucc Q) F).symm
  have hdegree := relatively_closed_polynomial_parameter_composite_degree_one
    t _ htrans F hF hvalue hclosed
  obtain ⟨a, b, ha, hform⟩ := relatively_closed_polynomial_parameter_constructs_affine_form
    t _ htrans F hF hvalue hclosed
  refine ⟨hdegree, a, b, ha, ?_⟩
  rw [hcomp, hform, map_add, map_mul, Polynomial.aeval_X]
  simp only [Polynomial.aeval_C, MvPolynomial.algebraMap_eq]

/-- A degree-at-most-two binary polynomial with zero quadratic part
has actual degree at most one. -/
theorem quadratic_polynomial_zero_quadratic_part_degree_le_one
    (Q : MvPolynomial (Fin 2) K) (hQ : Q.totalDegree ≤ 2) (hQ₂ : homogeneousComponent 2 Q = 0) :
    Q.totalDegree ≤ 1 := by
  by_contra! hlarge
  have hQ0 : Q ≠ 0 := by intro hz; simp [hz] at hlarge
  have hdegree : Q.totalDegree = 2 := by omega
  have htop := top_homogeneousComponent_ne_zero Q hQ0
  rw [hdegree, hQ₂] at htop
  exact htop rfl

variable [CharZero K]

/-- Independent actual affine tangent fields of the constructed
primitive Gauss parameter produce its full quadratic graph form, with a
nonzero affine parameter slope. Relative closedness and degree-one
linearity are derived from the original closed Gauss field. -/
theorem actual_conjugate_gauss_independent_tangents_construct_quadratic_graph_parameter
    (H : Fin 4 → MvPolynomial (Fin 4) K) (I : ImageRelationWitness H)
    (e : RatFunc K ≃ₐ[K] closedGaussParameterField H I) (f : S₀ ≃ₐ[K] S₀)
    (t : S₀) (ht : t = f (closedGaussParameterSourceHom H I e RatFunc.X))
    (P : MvPolynomial (Fin 3) K) (hchart : t = aeval x₀ P) (hPw : pderiv (2 : Fin 3) P ≠ 0)
    (u v : Fin 2 → K) (hdir : LinearIndependent K ![u, v])
    (β₁ β₂ : Fin 3 → K) (hu : affineProjectedTangentAction u β₁ P = 0)
    (hv : affineProjectedTangentAction v β₂ P = 0) :
    ∃ Q : MvPolynomial (Fin 2) K, Q.totalDegree ≤ 2 ∧
      ∃ a b : K, a ≠ 0 ∧ P = C a * (X 2 - rename Fin.castSucc Q) + C b := by
  obtain ⟨Q, F, hQ, hF, hcomp⟩ := independent_affine_tangent_fields_construct_quadratic_composite_parameter
    P hPw u v hdir β₁ β₂ hu hv
  obtain ⟨_hdegree, a, b, ha, hgraph⟩ := actual_conjugate_gauss_affine_composite_parameter_constructs_affine_graph
    H I e f t ht P hchart Q F hF hcomp
  exact ⟨Q, hQ, a, b, ha, hgraph⟩

end DimensionFourDependence
