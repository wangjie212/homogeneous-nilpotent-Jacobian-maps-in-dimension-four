import DimensionFourDependence.ParameterAlgebraicFieldExtension
import DimensionFourDependence.SpecifiedSimpleRootDirection
import DimensionFourDependence.FiniteGaussBoundaryPoint
import DimensionFourDependence.ParametricGraphBaseChange

/-! # The same finite fixed root controls all further coordinate fields

Keep the original finite root covectors and their specified dual ruling
vectors. Their coefficient algebraicity and dual values persist in every
specified coordinate-field embedding. The actual modified boundary
equation forces the same root kernel there. Every nonzero such direction
is a nonzero multiple of the same original finite fixed vector.
-/

namespace DimensionFourDependence

open Matrix Module

variable {K F R : Type*} [Field K] [CharZero K] [Field F] [Field R] [Algebra K F] [Algebra K R]

/-- The original finite root data force the fixed root in every
further coordinate field using the same specified longitudinal vector. -/
theorem finite_root_boundary_direction_fixed_after_field_embedding
    (p : RatFunc K →ₐ[K] F) (g : F →ₐ[K] R)
    (delta : Fin 3 → Derivation K R R) (y : Fin 3 → F)
    (hcoord : ∀ i j, delta i (g (y j)) = if j = i then 1 else 0)
    (A : Fin 3 → RatFunc K)
    (htangent : (fun i => p (rationalParameterDerivative K (A i))) ⬝ᵥ y = 0)
    (hfirst : (fun i => p (rationalParameterDerivative K (A i))) ≠ 0)
    (C : IntermediateField p.fieldRange F) [Module.Finite p.fieldRange C]
    (m s b : Fin 3 → C) (hb : b ∈ finiteParameterGraphRuling p C A)
    (hmb : m ⬝ᵥ b = 1) (hsb : s ⬝ᵥ b = 0)
    {d : ℕ} (hd : 1 < d) (rho c : F) (hrho : rho ≠ 0)
    (hfactor : parametricRulingDenominator p A y * c = ((fun i => (m i : F)) ⬝ᵥ y) * rho)
    (hroot : rho ^ d = (fun i => (s i : F)) ⬝ᵥ y)
    (v : Fin 3 → R) (hv : (fun i => (g.comp p) (rationalParameterDerivative K (A i))) ⬝ᵥ v = 0)
    (halg : ∀ i, IsAlgebraic (g.comp p).fieldRange (v i))
    (hboundary : matrixBilinearPairing (derivationHessian delta (g c)) v v -
      (2 / 3 : R) * (parametricGraphCubicCovector (g.comp p) A (fun i => g (y i)) ⬝ᵥ v) *
        ((fun i => delta i (g c)) ⬝ᵥ v) = 0) :
    (fun i => g (s i : F)) ⬝ᵥ v = 0 := by
  have htangentR : (fun i => (g.comp p) (rationalParameterDerivative K (A i))) ⬝ᵥ
      (fun i => g (y i)) = 0 := by
    simpa only [dotProduct, map_sum, map_mul, map_zero, AlgHom.comp_apply] using congrArg g htangent
  have hfirstR : (fun i => (g.comp p) (rationalParameterDerivative K (A i))) ≠ 0 := by
    intro hzero
    apply hfirst
    funext i
    apply g.injective
    change g (p (rationalParameterDerivative K (A i))) = g (0 : F)
    simpa only [map_zero, AlgHom.comp_apply, Pi.zero_apply] using congrFun hzero i
  have hbR : (fun i => (g.comp p) (rationalParameterDerivative K (A i))) ⬝ᵥ
      (fun i => g (b i : F)) = 0 := by
    simpa only [dotProduct, map_sum, map_mul, map_zero, AlgHom.comp_apply] using
      congrArg g (finiteParameterGraphRuling_original_pairing p C A b hb)
  have hmbR : (fun i => g (m i : F)) ⬝ᵥ (fun i => g (b i : F)) = 1 := by
    simpa only [dotProduct, map_sum, map_mul, map_one, IntermediateField.algebraMap_apply] using
      congrArg g (congrArg (algebraMap C F) hmb)
  have hsbR : (fun i => g (s i : F)) ⬝ᵥ (fun i => g (b i : F)) = 0 := by
    simpa only [dotProduct, map_sum, map_mul, map_zero, IntermediateField.algebraMap_apply] using
      congrArg g (congrArg (algebraMap C F) hsb)
  have hfactorR : parametricRulingDenominator (g.comp p) A (fun i => g (y i)) * g c =
      ((fun i => g (m i : F)) ⬝ᵥ (fun i => g (y i))) * g rho := by
    rw [parametricRulingDenominator_map]
    simpa only [map_mul, dotProduct, map_sum] using congrArg g hfactor
  have hrootR : g rho ^ d = (fun i => g (s i : F)) ⬝ᵥ (fun i => g (y i)) := by
    simpa only [map_pow, dotProduct, map_sum, map_mul] using congrArg g hroot
  exact parametric_simple_root_boundary_fixed_of_specified_dual_direction (g.comp p) delta
    (fun i => g (y i)) hcoord A htangentR hfirstR
    (fun i => g (m i : F)) (fun i => g (s i : F)) (fun i => g (b i : F))
    (fun i => parameter_algebraic_coefficient_map p g (m i : F)
      (finite_parameter_extension_coefficient_algebraic p C (m i)))
    (fun i => parameter_algebraic_coefficient_map p g (s i : F)
      (finite_parameter_extension_coefficient_algebraic p C (s i)))
    hbR hmbR hsbR hd (g rho) (g c) ((map_ne_zero g).mpr hrho) hfactorR hrootR v hv halg hboundary

/-- Every nonzero boundary direction in every further coordinate
field is proportional to the same specified original finite dual vector. -/
theorem finite_root_boundary_multiple_of_same_dual_point_after_field_embedding
    (p : RatFunc K →ₐ[K] F) (g : F →ₐ[K] R)
    (delta : Fin 3 → Derivation K R R) (y : Fin 3 → F)
    (hcoord : ∀ i j, delta i (g (y j)) = if j = i then 1 else 0)
    (A : Fin 3 → RatFunc K)
    (htangent : (fun i => p (rationalParameterDerivative K (A i))) ⬝ᵥ y = 0)
    (hfirst : (fun i => p (rationalParameterDerivative K (A i))) ≠ 0)
    (C : IntermediateField p.fieldRange F) [Module.Finite p.fieldRange C]
    (m s b z : Fin 3 → C)
    (hpair : LinearIndependent C ![rulingFormRestriction (finiteParameterGraphRuling p C A) m,
      rulingFormRestriction (finiteParameterGraphRuling p C A) s])
    (hb : b ∈ finiteParameterGraphRuling p C A) (hz : z ∈ finiteParameterGraphRuling p C A)
    (hmb : m ⬝ᵥ b = 1) (hsb : s ⬝ᵥ b = 0) (hmz : m ⬝ᵥ z = 0) (hsz : s ⬝ᵥ z = 1)
    {d : ℕ} (hd : 1 < d) (rho c : F) (hrho : rho ≠ 0)
    (hfactor : parametricRulingDenominator p A y * c = ((fun i => (m i : F)) ⬝ᵥ y) * rho)
    (hroot : rho ^ d = (fun i => (s i : F)) ⬝ᵥ y)
    (v : Fin 3 → R) (hv0 : v ≠ 0)
    (hv : (fun i => (g.comp p) (rationalParameterDerivative K (A i))) ⬝ᵥ v = 0)
    (halg : ∀ i, IsAlgebraic (g.comp p).fieldRange (v i))
    (hboundary : matrixBilinearPairing (derivationHessian delta (g c)) v v -
      (2 / 3 : R) * (parametricGraphCubicCovector (g.comp p) A (fun i => g (y i)) ⬝ᵥ v) *
        ((fun i => delta i (g c)) ⬝ᵥ v) = 0) :
    ∃ t : R, t ≠ 0 ∧ v = t • (fun i => g (b i : F)) := by
  have hs := finite_root_boundary_direction_fixed_after_field_embedding p g delta y hcoord A htangent hfirst
    C m s b hb hmb hsb hd rho c hrho hfactor hroot v hv halg hboundary
  let : Algebra F R := g.toRingHom.toAlgebra
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
  have hvB : B.map (algebraMap C R) *ᵥ v = 0 := by
    funext j
    change (fun i => g (finiteParameterGraphNormal p C A i : F)) ⬝ᵥ v = 0
    simpa only [finiteParameterGraphNormal_value, AlgHom.comp_apply] using hv
  have hcoordinates := matrix_kernel_coordinate_form_span_after_extension B m s b z hspan v hvB
  have hrep : v = ((fun i => g (m i : F)) ⬝ᵥ v) • (fun i => g (b i : F)) := by
    funext i
    change v i = ((fun j => g (m j : F)) ⬝ᵥ v) * g (b i : F)
    have hi := hcoordinates i
    change v i = g (b i : F) * ((fun j => g (m j : F)) ⬝ᵥ v) +
      g (z i : F) * ((fun j => g (s j : F)) ⬝ᵥ v) at hi
    rw [hs, mul_zero, add_zero] at hi
    exact hi.trans (mul_comm _ _)
  refine ⟨(fun i => g (m i : F)) ⬝ᵥ v, ?_, hrep⟩
  intro ht
  apply hv0
  rw [hrep, ht, zero_smul]

end DimensionFourDependence
