import DimensionFourDependence.FiniteParameterGraphRuling
import DimensionFourDependence.SpecifiedRulingDualCoordinates
import DimensionFourDependence.HomogeneousProjectiveSubstitution
import DimensionFourDependence.ProjectiveInfinityChartLocalBound

/-! # The specified simple-root chart point is the actual boundary point

The coordinate reconstruction uses the very same dual pair used in
the length-two chart. Thus every nonzero parameter-algebraic boundary
direction represents that chosen point in the original projective
spectrum, and membership in the actual closure transfers to it.
-/

namespace DimensionFourDependence

open Matrix Module

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

/-- The specified dual pair reconstructs all coordinates of the
actual graph ruling over the output field. -/
theorem finite_parameter_graph_coordinates_of_specified_dual_pair
    (p : RatFunc K →ₐ[K] F) (C : IntermediateField p.fieldRange F)
    (A : Fin 3 → RatFunc K)
    (hfirst : (fun i => p (rationalParameterDerivative K (A i))) ≠ 0)
    (m s b z : Fin 3 → C)
    (hpair : LinearIndependent C ![rulingFormRestriction (finiteParameterGraphRuling p C A) m,
      rulingFormRestriction (finiteParameterGraphRuling p C A) s])
    (hb : b ∈ finiteParameterGraphRuling p C A) (hz : z ∈ finiteParameterGraphRuling p C A)
    (hmb : m ⬝ᵥ b = 1) (hsb : s ⬝ᵥ b = 0)
    (hmz : m ⬝ᵥ z = 0) (hsz : s ⬝ᵥ z = 1)
    (v : Fin 3 → F) (hv : (fun i => p (rationalParameterDerivative K (A i))) ⬝ᵥ v = 0) :
    ∀ i, v i = (b i : F) * ((fun j => (m j : F)) ⬝ᵥ v) +
      (z i : F) * ((fun j => (s j : F)) ⬝ᵥ v) := by
  let B : Matrix (Fin 1) (Fin 3) C := fun _ i => finiteParameterGraphNormal p C A i
  have hWE : finiteParameterGraphRuling p C A = LinearMap.ker B.toLin' := by
    ext x
    change finiteParameterGraphNormal p C A ⬝ᵥ x = 0 ↔ B *ᵥ x = 0
    constructor
    · intro hx
      funext j
      exact hx
    · intro hx
      exact congrFun hx 0
  have hspan : ∀ x ∈ LinearMap.ker B.toLin', ∀ i,
      x i = b i * (m ⬝ᵥ x) + z i * (s ⬝ᵥ x) := by
    rw [← hWE]
    exact ruling_coordinates_of_specified_dual_pair _ (finiteParameterGraphRuling_finrank p C A hfirst)
      m s b z hpair hb hz hmb hsb hmz hsz
  have hvB : B.map (algebraMap C F) *ᵥ v = 0 := by
    funext j
    change (fun i => algebraMap C F (finiteParameterGraphNormal p C A i)) ⬝ᵥ v = 0
    simpa only [IntermediateField.algebraMap_apply, finiteParameterGraphNormal_value] using hv
  exact matrix_kernel_coordinate_form_span_after_extension B m s b z hspan v hvB

/-- A nonzero proportional direction transfers membership in the
actual projective closure to the specified infinity-chart point. -/
theorem projective_closure_infinity_point_of_nonzero_smul
    {G : Type*} [Field G] [Algebra F G]
    (x : Fin 3 → G) (v b : Fin 3 → F) (hv : v ≠ 0)
    (hpoint : projectiveFieldPoint (E := F) (fun j : Option (Fin 3) => j.elim 0 v)
      (infinity_direction_projective_coordinates_ne_zero v hv) ∈ projectiveClosureSet (L := F) x)
    (t : F) (ht : t ≠ 0) (hrep : v = t • b) :
    ∃ hb : b ≠ 0,
      projectiveFieldPoint (E := F) (fun j : Option (Fin 3) => j.elim 0 b)
        (infinity_direction_projective_coordinates_ne_zero b hb) ∈ projectiveClosureSet (L := F) x := by
  have hb : b ≠ 0 := by
    intro hzero
    apply hv
    rw [hrep, hzero, smul_zero]
  refine ⟨hb, ?_⟩
  have he := projectiveFieldPoint_eq_of_proportional (K := F)
    (fun j : Option (Fin 3) => j.elim 0 v) (fun j : Option (Fin 3) => j.elim 0 b)
    (infinity_direction_projective_coordinates_ne_zero v hv)
    (infinity_direction_projective_coordinates_ne_zero b hb) t ht (by
      intro j
      cases j with
      | none => simp
      | some i => exact congrFun hrep i)
  rwa [he] at hpoint

variable [CharZero K]

/-- Every actual nonzero parameter-algebraic boundary direction is
a nonzero scalar multiple of the specified simple-root chart vector. -/
theorem finite_parameter_graph_boundary_multiple_of_specified_dual_point
    (p : RatFunc K →ₐ[K] F) (delta : Fin 3 → Derivation K F F) (y : Fin 3 → F)
    (hcoord : ∀ i j, delta i (y j) = if j = i then 1 else 0)
    (A : Fin 3 → RatFunc K)
    (htangent : (fun i => p (rationalParameterDerivative K (A i))) ⬝ᵥ y = 0)
    (hfirst : (fun i => p (rationalParameterDerivative K (A i))) ≠ 0)
    (C : IntermediateField p.fieldRange F) [Module.Finite p.fieldRange C]
    (m s b z : Fin 3 → C)
    (hpair : LinearIndependent C ![rulingFormRestriction (finiteParameterGraphRuling p C A) m,
      rulingFormRestriction (finiteParameterGraphRuling p C A) s])
    (hb : b ∈ finiteParameterGraphRuling p C A) (hz : z ∈ finiteParameterGraphRuling p C A)
    (hmb : m ⬝ᵥ b = 1) (hsb : s ⬝ᵥ b = 0)
    (hmz : m ⬝ᵥ z = 0) (hsz : s ⬝ᵥ z = 1)
    {d : ℕ} (hd : 1 < d) (rho c : F) (hrho : rho ≠ 0)
    (hfactor : parametricRulingDenominator p A y * c = ((fun i => (m i : F)) ⬝ᵥ y) * rho)
    (hroot : rho ^ d = (fun i => (s i : F)) ⬝ᵥ y)
    (v : Fin 3 → F) (hv0 : v ≠ 0)
    (hv : (fun i => p (rationalParameterDerivative K (A i))) ⬝ᵥ v = 0)
    (halg : ∀ i, IsAlgebraic p.fieldRange (v i))
    (hboundary : matrixBilinearPairing (derivationHessian delta c) v v -
      (2 / 3 : F) * (parametricGraphCubicCovector p A y ⬝ᵥ v) * ((fun i => delta i c) ⬝ᵥ v) = 0) :
    ∃ t : F, t ≠ 0 ∧ v = t • (fun i => (b i : F)) := by
  have hs := finite_parameter_graph_simple_root_boundary_direction_fixed p delta y hcoord A htangent hfirst
    C m s hpair hd rho c hrho hfactor hroot v hv halg hboundary
  have hcoordinates := finite_parameter_graph_coordinates_of_specified_dual_pair p C A hfirst
    m s b z hpair hb hz hmb hsb hmz hsz v hv
  have hrep : v = ((fun i => (m i : F)) ⬝ᵥ v) • (fun i => (b i : F)) := by
    funext i
    change v i = ((fun j => (m j : F)) ⬝ᵥ v) * (b i : F)
    simpa only [hs, mul_zero, add_zero, mul_comm] using hcoordinates i
  refine ⟨(fun i => (m i : F)) ⬝ᵥ v, ?_, hrep⟩
  intro ht
  apply hv0
  rw [hrep, ht, zero_smul]

end DimensionFourDependence
