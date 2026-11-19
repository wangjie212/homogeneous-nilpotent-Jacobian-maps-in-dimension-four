import DimensionFourDependence.SimpleFixedRootHessian
import DimensionFourDependence.RulingCoordinateBasis

/-! # The simple fixed root for actual parameter-algebraic ruling directions

Independent root forms on a two-dimensional parameter-defined ruling
construct a longitudinal vector and its actual coordinate derivation.
The graph parameter equation shows that this derivation fixes the
parameter. The factorized Hessian therefore forces every algebraic
zero-acceleration direction into the kernel of the root form.

Applying the original modified-quadric boundary equation derives the
zero acceleration as well. No longitudinal vector or varying-root
exclusion is assumed.
-/

namespace DimensionFourDependence

open Matrix Module

variable {K F : Type*} [Field K] [CharZero K] [Field F] [Algebra K F] {n : ℕ}

omit [CharZero K] in
/-- Finite sums of products of parameter-algebraic coefficients are
parameter-algebraic, including all direction-coordinate pairings. -/
theorem algebraic_covector_direction_pairing
    (p : RatFunc K →ₐ[K] F) (m v : Fin n → F)
    (hm : ∀ i, IsAlgebraic p.fieldRange (m i))
    (hv : ∀ i, IsAlgebraic p.fieldRange (v i)) :
    IsAlgebraic p.fieldRange (m ⬝ᵥ v) := by
  classical
  have hsum (t : Finset (Fin n)) : IsAlgebraic p.fieldRange (∑ i ∈ t, m i * v i) := by
    induction t using Finset.induction_on with
    | empty => simpa using (isAlgebraic_zero : IsAlgebraic p.fieldRange (0 : F))
    | @insert i t hi ih => simpa only [Finset.sum_insert hi] using ((hm i).mul (hv i)).add ih
  exact hsum Finset.univ

/-- The actual direction derivative of a parameter-algebraic
covector is its original coordinate pairing with the direction. -/
theorem parameter_algebraic_covector_direction_derivative
    (p : RatFunc K →ₐ[K] F) (δ : Fin n → Derivation K F F) (y v m : Fin n → F)
    (hcoord : ∀ i j, δ i (y j) = if j = i then 1 else 0)
    (ht : coordinateEuler v δ (p RatFunc.X) = 0)
    (hm : ∀ i, IsAlgebraic p.fieldRange (m i)) :
    coordinateEuler v δ (m ⬝ᵥ y) = m ⬝ᵥ v := by
  have hc (i : Fin n) : coordinateEuler v δ (m i) = 0 :=
    parameter_algebraic_coefficient_direction_constant p (coordinateEuler v δ) ht (m i) (hm i)
  rw [derivation_dotProduct]
  simp only [hc, dotProduct, zero_mul, Finset.sum_const_zero, zero_add,
    coordinate_direction_coordinate δ y v hcoord]

/-- A finite parameter extension supplies all coefficient algebraicity
in its given realization inside the target field. -/
theorem finite_parameter_extension_coefficient_algebraic
    (p : RatFunc K →ₐ[K] F) (C : IntermediateField p.fieldRange F)
    [Module.Finite p.fieldRange C] (c : C) : IsAlgebraic p.fieldRange (c : F) := by
  exact (Algebra.IsAlgebraic.isAlgebraic (R := p.fieldRange) c).algebraMap

/-- Independent forms on the actual parameter-defined ruling
construct the longitudinal derivation and force every algebraic
zero-acceleration direction to annihilate the transverse root form. -/
theorem parametric_independent_root_forms_zero_acceleration_direction_fixed
    (p : RatFunc K →ₐ[K] F) (δ : Fin n → Derivation K F F) (y : Fin n → F)
    (hcoord : ∀ i j, δ i (y j) = if j = i then 1 else 0)
    (A : Fin n → RatFunc K)
    (htangent : (fun i => p (rationalParameterDerivative K (A i))) ⬝ᵥ y = 0)
    (hfirst : (fun i => p (rationalParameterDerivative K (A i))) ≠ 0)
    (C : IntermediateField p.fieldRange F) [Module.Finite p.fieldRange C]
    (W : Submodule C (Fin n → C)) (hdim : finrank C W = 2)
    (hW : ∀ b ∈ W, (fun i => p (rationalParameterDerivative K (A i))) ⬝ᵥ (fun i => (b i : F)) = 0)
    (m s : Fin n → C)
    (hpair : LinearIndependent C ![rulingFormRestriction W m, rulingFormRestriction W s])
    {d : ℕ} (hd : 1 < d) (rho : F) (hrho : rho ≠ 0)
    (hroot : rho ^ d = (fun i => (s i : F)) ⬝ᵥ y)
    (v : Fin n → F) (hv : (fun i => p (rationalParameterDerivative K (A i))) ⬝ᵥ v = 0)
    (halg : ∀ i, IsAlgebraic p.fieldRange (v i))
    (hsecond : coordinateEuler v δ (coordinateEuler v δ (((fun i => (m i : F)) ⬝ᵥ y) * rho)) = 0) :
    (fun i => (s i : F)) ⬝ᵥ v = 0 := by
  let : CharZero F := charZero_of_injective_algebraMap (algebraMap K F).injective
  obtain ⟨bM, _bS, _hLI, hbM, _hbS, hMbM, hSbM, _hMbS, _hSbS, _hspan⟩ :=
    two_dimensional_ruling_coordinate_basis W hdim m s hpair
  let D := coordinateEuler v δ
  let b : Fin n → F := fun i => (bM i : F)
  let R := coordinateEuler b δ
  let r : F := (fun i => (m i : F)) ⬝ᵥ y
  let z : F := (fun i => (s i : F)) ⬝ᵥ y
  have htD : D (p RatFunc.X) = 0 :=
    parametric_ruling_direction_fixes_parameter p δ y hcoord A htangent hfirst v hv
  have htR : R (p RatFunc.X) = 0 :=
    parametric_ruling_direction_fixes_parameter p δ y hcoord A htangent hfirst b (hW bM hbM)
  have hm (i : Fin n) : IsAlgebraic p.fieldRange (m i : F) :=
    finite_parameter_extension_coefficient_algebraic p C (m i)
  have hs (i : Fin n) : IsAlgebraic p.fieldRange (s i : F) :=
    finite_parameter_extension_coefficient_algebraic p C (s i)
  have hrR : R r = 1 := by
    rw [show R r = coordinateEuler b δ ((fun i => (m i : F)) ⬝ᵥ y) from rfl,
      parameter_algebraic_covector_direction_derivative p δ y b _ hcoord htR hm]
    change (fun i => algebraMap C F (m i)) ⬝ᵥ (fun i => algebraMap C F (bM i)) = 1
    simpa only [dotProduct, map_sum, map_mul, map_one] using congrArg (algebraMap C F) hMbM
  have hzR : R z = 0 := by
    rw [show R z = coordinateEuler b δ ((fun i => (s i : F)) ⬝ᵥ y) from rfl,
      parameter_algebraic_covector_direction_derivative p δ y b _ hcoord htR hs]
    change (fun i => algebraMap C F (s i)) ⬝ᵥ (fun i => algebraMap C F (bM i)) = 0
    simpa only [dotProduct, map_sum, map_mul, map_zero] using congrArg (algebraMap C F) hSbM
  have hrD : D r = (fun i => (m i : F)) ⬝ᵥ v :=
    parameter_algebraic_covector_direction_derivative p δ y v _ hcoord htD hm
  have hzD : D z = (fun i => (s i : F)) ⬝ᵥ v :=
    parameter_algebraic_covector_direction_derivative p δ y v _ hcoord htD hs
  have hu : IsAlgebraic p.fieldRange (D r) := by
    rw [hrD]
    exact algebraic_covector_direction_pairing p _ v hm halg
  have hv' : IsAlgebraic p.fieldRange (D z) := by
    rw [hzD]
    exact algebraic_covector_direction_pairing p _ v hs halg
  have hacc : D (D ((1 * r + 0 * z) * rho)) = 0 := by
    simpa only [one_mul, zero_mul, add_zero] using hsecond
  have hfixed := parameter_algebraic_zero_acceleration_has_fixed_root p D R htD htR hd r z rho 1 0
    hrho hroot one_ne_zero hrR hzR isAlgebraic_one isAlgebraic_zero hu hv' hacc
  rwa [hzD] at hfixed

/-- The original modified-quadric boundary equation derives the
acceleration input internally. Every parameter-algebraic boundary
direction in the simple case is the fixed root of the actual root form. -/
theorem parametric_independent_root_forms_modified_boundary_direction_fixed
    (p : RatFunc K →ₐ[K] F) (δ : Fin n → Derivation K F F) (y : Fin n → F)
    (hcoord : ∀ i j, δ i (y j) = if j = i then 1 else 0)
    (A : Fin n → RatFunc K)
    (htangent : (fun i => p (rationalParameterDerivative K (A i))) ⬝ᵥ y = 0)
    (hfirst : (fun i => p (rationalParameterDerivative K (A i))) ≠ 0)
    (C : IntermediateField p.fieldRange F) [Module.Finite p.fieldRange C]
    (W : Submodule C (Fin n → C)) (hdim : finrank C W = 2)
    (hW : ∀ b ∈ W, (fun i => p (rationalParameterDerivative K (A i))) ⬝ᵥ (fun i => (b i : F)) = 0)
    (m s : Fin n → C)
    (hpair : LinearIndependent C ![rulingFormRestriction W m, rulingFormRestriction W s])
    {d : ℕ} (hd : 1 < d) (rho c : F) (hrho : rho ≠ 0)
    (hfactor : parametricRulingDenominator p A y * c = ((fun i => (m i : F)) ⬝ᵥ y) * rho)
    (hroot : rho ^ d = (fun i => (s i : F)) ⬝ᵥ y)
    (v : Fin n → F) (hv : (fun i => p (rationalParameterDerivative K (A i))) ⬝ᵥ v = 0)
    (halg : ∀ i, IsAlgebraic p.fieldRange (v i))
    (hboundary : matrixBilinearPairing (derivationHessian δ c) v v -
      (2 / 3 : F) * (parametricGraphCubicCovector p A y ⬝ᵥ v) * ((fun i => δ i c) ⬝ᵥ v) = 0) :
    (fun i => (s i : F)) ⬝ᵥ v = 0 := by
  have hsecond := parametric_ruling_zero_acceleration_of_modified_boundary p δ y hcoord A htangent hfirst
    v hv halg c hboundary
  rw [hfactor] at hsecond
  exact parametric_independent_root_forms_zero_acceleration_direction_fixed p δ y hcoord A htangent hfirst
    C W hdim hW m s hpair hd rho hrho hroot v hv halg hsecond

end DimensionFourDependence
