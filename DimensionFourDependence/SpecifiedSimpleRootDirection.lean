import DimensionFourDependence.ParametricSimpleFixedRoot

/-! # The fixed-root conclusion using the specified dual longitudinal vector

The longitudinal vector may already have been constructed over a
smaller finite parameter field. Only its actual dual values and ruling
equation are needed in a further coordinate field, together with the
mapped parameter algebraicity. Thus no new finite coefficient field
or independently chosen dual basis is needed at each infinity prime.
-/

namespace DimensionFourDependence

open Matrix

variable {K F : Type*} [Field K] [CharZero K] [Field F] [Algebra K F] {n : ℕ}

/-- The actual modified boundary equation forces the fixed root
using a specified longitudinal ruling vector and its two dual values. -/
theorem parametric_simple_root_boundary_fixed_of_specified_dual_direction
    (p : RatFunc K →ₐ[K] F) (delta : Fin n → Derivation K F F) (y : Fin n → F)
    (hcoord : ∀ i j, delta i (y j) = if j = i then 1 else 0)
    (A : Fin n → RatFunc K)
    (htangent : (fun i => p (rationalParameterDerivative K (A i))) ⬝ᵥ y = 0)
    (hfirst : (fun i => p (rationalParameterDerivative K (A i))) ≠ 0)
    (m s b : Fin n → F)
    (hm : ∀ i, IsAlgebraic p.fieldRange (m i))
    (hs : ∀ i, IsAlgebraic p.fieldRange (s i))
    (hb : (fun i => p (rationalParameterDerivative K (A i))) ⬝ᵥ b = 0)
    (hmb : m ⬝ᵥ b = 1) (hsb : s ⬝ᵥ b = 0)
    {d : ℕ} (hd : 1 < d) (rho c : F) (hrho : rho ≠ 0)
    (hfactor : parametricRulingDenominator p A y * c = (m ⬝ᵥ y) * rho)
    (hroot : rho ^ d = s ⬝ᵥ y)
    (v : Fin n → F) (hv : (fun i => p (rationalParameterDerivative K (A i))) ⬝ᵥ v = 0)
    (halg : ∀ i, IsAlgebraic p.fieldRange (v i))
    (hboundary : matrixBilinearPairing (derivationHessian delta c) v v -
      (2 / 3 : F) * (parametricGraphCubicCovector p A y ⬝ᵥ v) * ((fun i => delta i c) ⬝ᵥ v) = 0) :
    s ⬝ᵥ v = 0 := by
  let : CharZero F := charZero_of_injective_algebraMap (algebraMap K F).injective
  let D := coordinateEuler v delta
  let R := coordinateEuler b delta
  let r := m ⬝ᵥ y
  let z := s ⬝ᵥ y
  have htD : D (p RatFunc.X) = 0 :=
    parametric_ruling_direction_fixes_parameter p delta y hcoord A htangent hfirst v hv
  have htR : R (p RatFunc.X) = 0 :=
    parametric_ruling_direction_fixes_parameter p delta y hcoord A htangent hfirst b hb
  have hrR : R r = 1 := by
    rw [show R r = coordinateEuler b delta (m ⬝ᵥ y) from rfl,
      parameter_algebraic_covector_direction_derivative p delta y b m hcoord htR hm, hmb]
  have hzR : R z = 0 := by
    rw [show R z = coordinateEuler b delta (s ⬝ᵥ y) from rfl,
      parameter_algebraic_covector_direction_derivative p delta y b s hcoord htR hs, hsb]
  have hrD : D r = m ⬝ᵥ v := parameter_algebraic_covector_direction_derivative p delta y v m hcoord htD hm
  have hzD : D z = s ⬝ᵥ v := parameter_algebraic_covector_direction_derivative p delta y v s hcoord htD hs
  have hu : IsAlgebraic p.fieldRange (D r) := by
    rw [hrD]
    exact algebraic_covector_direction_pairing p m v hm halg
  have hv' : IsAlgebraic p.fieldRange (D z) := by
    rw [hzD]
    exact algebraic_covector_direction_pairing p s v hs halg
  have hsecond := parametric_ruling_zero_acceleration_of_modified_boundary p delta y hcoord A htangent hfirst
    v hv halg c hboundary
  rw [hfactor] at hsecond
  have hacc : D (D ((1 * r + 0 * z) * rho)) = 0 := by
    simpa only [one_mul, zero_mul, add_zero] using hsecond
  have hfixed := parameter_algebraic_zero_acceleration_has_fixed_root p D R htD htR hd r z rho 1 0
    hrho hroot one_ne_zero hrR hzR isAlgebraic_one isAlgebraic_zero hu hv' hacc
  rwa [hzD] at hfixed

end DimensionFourDependence
