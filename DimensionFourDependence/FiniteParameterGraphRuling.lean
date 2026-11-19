import DimensionFourDependence.ParametricSimpleFixedRoot

/-! # The actual graph ruling over a finite parameter extension

The original first derivative of the graph slope defines the ruling
over the given parameter coefficient field. Its nonzero original value
constructs a surjective linear functional, hence a two-dimensional
kernel. Mapping this kernel to the output field gives the actual graph
ruling. The simple-root boundary conclusion therefore needs no supplied
two-dimensional ruling or longitudinal direction.
-/

namespace DimensionFourDependence

open Matrix Module

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

/-- The original first graph-normal derivative in the actual finite
parameter coefficient field. -/
noncomputable def finiteParameterGraphNormal
    (p : RatFunc K →ₐ[K] F) (C : IntermediateField p.fieldRange F)
    (A : Fin 3 → RatFunc K) : Fin 3 → C :=
  fun i => algebraMap p.fieldRange C (p.equivFieldRange (rationalParameterDerivative K (A i)))

/-- The graph ruling over its actual finite parameter coefficients. -/
noncomputable def finiteParameterGraphRuling
    (p : RatFunc K →ₐ[K] F) (C : IntermediateField p.fieldRange F)
    (A : Fin 3 → RatFunc K) : Submodule C (Fin 3 → C) :=
  LinearMap.ker (dotProductBilin C C (finiteParameterGraphNormal p C A))

/-- The coefficient normal has exactly its original output-field value. -/
theorem finiteParameterGraphNormal_value
    (p : RatFunc K →ₐ[K] F) (C : IntermediateField p.fieldRange F)
    (A : Fin 3 → RatFunc K) (i : Fin 3) :
    (finiteParameterGraphNormal p C A i : F) = p (rationalParameterDerivative K (A i)) := rfl

/-- The original nonzero normal remains nonzero in the actual
parameter coefficient field. -/
theorem finiteParameterGraphNormal_ne_zero
    (p : RatFunc K →ₐ[K] F) (C : IntermediateField p.fieldRange F)
    (A : Fin 3 → RatFunc K)
    (hfirst : (fun i => p (rationalParameterDerivative K (A i))) ≠ 0) :
    finiteParameterGraphNormal p C A ≠ 0 := by
  intro hz
  apply hfirst
  funext i
  rw [← finiteParameterGraphNormal_value p C A i, hz]
  rfl

/-- The actual graph ruling has dimension two; this is derived from
the original nonzero graph-normal derivative. -/
theorem finiteParameterGraphRuling_finrank
    (p : RatFunc K →ₐ[K] F) (C : IntermediateField p.fieldRange F)
    (A : Fin 3 → RatFunc K)
    (hfirst : (fun i => p (rationalParameterDerivative K (A i))) ≠ 0) :
    finrank C (finiteParameterGraphRuling p C A) = 2 := by
  classical
  let alpha := finiteParameterGraphNormal p C A
  have hn : alpha ≠ 0 := finiteParameterGraphNormal_ne_zero p C A hfirst
  obtain ⟨i, hi⟩ : ∃ i, alpha i ≠ 0 := by
    simpa only [ne_eq, funext_iff, Pi.zero_apply, not_forall] using hn
  let L := dotProductBilin C C alpha
  have hsurj : Function.Surjective L := by
    intro x
    refine ⟨Pi.single i (x / alpha i), ?_⟩
    change alpha ⬝ᵥ Pi.single i (x / alpha i) = x
    rw [dotProduct_single]
    field_simp
  have he := LinearMap.finrank_range_add_finrank_ker L
  rw [LinearMap.range_eq_top.mpr hsurj] at he
  simp only [finrank_top, finrank_self, Module.finrank_pi, Fintype.card_fin] at he
  change finrank C (LinearMap.ker L) = 2
  omega

/-- Every coefficient-field ruling vector lies in the actual original
graph ruling after its specified coefficient embedding. -/
theorem finiteParameterGraphRuling_original_pairing
    (p : RatFunc K →ₐ[K] F) (C : IntermediateField p.fieldRange F)
    (A : Fin 3 → RatFunc K) (b : Fin 3 → C) (hb : b ∈ finiteParameterGraphRuling p C A) :
    (fun i => p (rationalParameterDerivative K (A i))) ⬝ᵥ (fun i => (b i : F)) = 0 := by
  change finiteParameterGraphNormal p C A ⬝ᵥ b = 0 at hb
  have he := congrArg (algebraMap C F) hb
  simpa only [dotProduct, map_sum, map_mul, map_zero, IntermediateField.algebraMap_apply,
    finiteParameterGraphNormal_value] using he

variable [CharZero K]

/-- The actual parameter normal constructs the ruling and the
longitudinal direction. The modified boundary equation then forces
every parameter-algebraic direction to be the simple fixed root. -/
theorem finite_parameter_graph_simple_root_boundary_direction_fixed
    (p : RatFunc K →ₐ[K] F) (δ : Fin 3 → Derivation K F F) (y : Fin 3 → F)
    (hcoord : ∀ i j, δ i (y j) = if j = i then 1 else 0)
    (A : Fin 3 → RatFunc K)
    (htangent : (fun i => p (rationalParameterDerivative K (A i))) ⬝ᵥ y = 0)
    (hfirst : (fun i => p (rationalParameterDerivative K (A i))) ≠ 0)
    (C : IntermediateField p.fieldRange F) [Module.Finite p.fieldRange C]
    (m s : Fin 3 → C)
    (hpair : LinearIndependent C
      ![rulingFormRestriction (finiteParameterGraphRuling p C A) m,
        rulingFormRestriction (finiteParameterGraphRuling p C A) s])
    {d : ℕ} (hd : 1 < d) (rho c : F) (hrho : rho ≠ 0)
    (hfactor : parametricRulingDenominator p A y * c = ((fun i => (m i : F)) ⬝ᵥ y) * rho)
    (hroot : rho ^ d = (fun i => (s i : F)) ⬝ᵥ y)
    (v : Fin 3 → F) (hv : (fun i => p (rationalParameterDerivative K (A i))) ⬝ᵥ v = 0)
    (halg : ∀ i, IsAlgebraic p.fieldRange (v i))
    (hboundary : matrixBilinearPairing (derivationHessian δ c) v v -
      (2 / 3 : F) * (parametricGraphCubicCovector p A y ⬝ᵥ v) * ((fun i => δ i c) ⬝ᵥ v) = 0) :
    (fun i => (s i : F)) ⬝ᵥ v = 0 :=
  parametric_independent_root_forms_modified_boundary_direction_fixed p δ y hcoord A htangent hfirst
    C (finiteParameterGraphRuling p C A) (finiteParameterGraphRuling_finrank p C A hfirst)
    (finiteParameterGraphRuling_original_pairing p C A) m s hpair hd rho c hrho hfactor hroot v hv halg hboundary

/-- The simple root is one constructed projective direction over the
finite parameter field. Every nonzero parameter-algebraic boundary
direction is a nonzero scalar multiple of this same vector. -/
theorem finite_parameter_graph_simple_root_boundary_direction_unique
    (p : RatFunc K →ₐ[K] F) (δ : Fin 3 → Derivation K F F) (y : Fin 3 → F)
    (hcoord : ∀ i j, δ i (y j) = if j = i then 1 else 0)
    (A : Fin 3 → RatFunc K)
    (htangent : (fun i => p (rationalParameterDerivative K (A i))) ⬝ᵥ y = 0)
    (hfirst : (fun i => p (rationalParameterDerivative K (A i))) ≠ 0)
    (C : IntermediateField p.fieldRange F) [Module.Finite p.fieldRange C]
    (m s : Fin 3 → C)
    (hpair : LinearIndependent C
      ![rulingFormRestriction (finiteParameterGraphRuling p C A) m,
        rulingFormRestriction (finiteParameterGraphRuling p C A) s])
    {d : ℕ} (hd : 1 < d) (rho c : F) (hrho : rho ≠ 0)
    (hfactor : parametricRulingDenominator p A y * c = ((fun i => (m i : F)) ⬝ᵥ y) * rho)
    (hroot : rho ^ d = (fun i => (s i : F)) ⬝ᵥ y) :
    ∃ b : Fin 3 → C, b ≠ 0 ∧ b ∈ finiteParameterGraphRuling p C A ∧ s ⬝ᵥ b = 0 ∧
      ∀ v : Fin 3 → F, v ≠ 0 →
        (fun i => p (rationalParameterDerivative K (A i))) ⬝ᵥ v = 0 →
        (∀ i, IsAlgebraic p.fieldRange (v i)) →
        matrixBilinearPairing (derivationHessian δ c) v v -
          (2 / 3 : F) * (parametricGraphCubicCovector p A y ⬝ᵥ v) * ((fun i => δ i c) ⬝ᵥ v) = 0 →
        ∃ t : F, t ≠ 0 ∧ v = t • (fun i => (b i : F)) := by
  obtain ⟨bM, bS, hLI, hbM, _hbS, _hMbM, hSbM, _hMbS, _hSbS, hspan⟩ :=
    two_dimensional_ruling_coordinate_basis (finiteParameterGraphRuling p C A)
      (finiteParameterGraphRuling_finrank p C A hfirst) m s hpair
  have hbM0 : bM ≠ 0 := by simpa using hLI.ne_zero (0 : Fin 2)
  refine ⟨bM, hbM0, hbM, hSbM, ?_⟩
  intro v hv0 hv halg hboundary
  have hszero := finite_parameter_graph_simple_root_boundary_direction_fixed p δ y hcoord A htangent hfirst
    C m s hpair hd rho c hrho hfactor hroot v hv halg hboundary
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
  have hspanB : ∀ x ∈ LinearMap.ker B.toLin', ∀ i,
      x i = bM i * (m ⬝ᵥ x) + bS i * (s ⬝ᵥ x) := by
    rw [← hWE]
    exact hspan
  have hvB : B.map (algebraMap C F) *ᵥ v = 0 := by
    funext j
    change (fun i => algebraMap C F (finiteParameterGraphNormal p C A i)) ⬝ᵥ v = 0
    simpa only [IntermediateField.algebraMap_apply, finiteParameterGraphNormal_value] using hv
  have hcoordinates := matrix_kernel_coordinate_form_span_after_extension B m s bM bS hspanB v hvB
  have hrep : v = ((fun i => (m i : F)) ⬝ᵥ v) • (fun i => (bM i : F)) := by
    funext i
    change v i = ((fun j => (m j : F)) ⬝ᵥ v) * (bM i : F)
    have hi := hcoordinates i
    simp only [IntermediateField.algebraMap_apply] at hi
    rw [hszero, mul_zero, add_zero] at hi
    exact hi.trans (mul_comm _ _)
  refine ⟨(fun i => (m i : F)) ⬝ᵥ v, ?_, hrep⟩
  intro ht
  apply hv0
  rw [hrep, ht, zero_smul]

end DimensionFourDependence
