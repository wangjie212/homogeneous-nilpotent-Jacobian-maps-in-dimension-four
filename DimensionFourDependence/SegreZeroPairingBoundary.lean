import DimensionFourDependence.SegreZeroPairingFiberEquations
import DimensionFourDependence.AffineFiberBoundaryLinearEquation

/-! # Section 5.4: every actual zero-pairing infinity direction kills the radial second invariant -/

namespace DimensionFourDependence

open MvPolynomial Matrix
attribute [local instance] MvPolynomial.gradedAlgebra

set_option maxHeartbeats 3000000

variable {K E F κ σ : Type*} [Field K] [Field E] [CharZero E] [Algebra K E]
    [Field F] [Algebra E F] [Field κ] [Algebra E κ]

/-- The actual zero-pairing fiber equations give D_b(rq)=0 at every
actual projective infinity point. The affine third equation and its
boundary covector, including its radial correction, are constructed. -/
theorem segre_zero_pairing_projective_boundary_radial_second_gradient_zero
    (δ : Fin 3 → Derivation K E E) (Y : Fin 3 → E)
    (hcoord : ∀ i j, δ i (Y j) = if j = i then 1 else 0) (hY0 : Y 0 ≠ 0)
    (x : σ → F) (z : Option σ → κ) (hz : z ≠ 0)
    (hpoint : projectiveFieldPoint (E := E) z hz ∈ projectiveClosureSet (L := E) x)
    (hz0 : z none = 0) (f : Fin 3 → σ) (q k : E)
    (hQ : aeval (x ∘ f) (quadraticFiberPolynomial 0 (derivationHessian δ (segreGraphFunction Y)) q) = 0)
    (hC : aeval (x ∘ f) (cubicFiberPolynomial (fun i => δ i q) 0
      (derivationCubicTensor δ (segreGraphFunction Y)) k) = 0) :
    ∑ i, algebraMap E κ (δ i (Y 0 * q)) * z (some (f i)) = 0 := by
  have he := segre_zero_pairing_cubic_equation_is_affine δ Y hcoord hY0 (x ∘ f) q k hQ hC
  have hb := affine_linear_fiber_equation_covector_vanishes_at_infinity x z hz hpoint hz0 f
    (segreZeroPairingThirdCovector δ Y q) k he
  have hr : algebraMap E κ (Y 0) ≠ 0 := (map_ne_zero (algebraMap E κ)).mpr hY0
  simp [segreZeroPairingThirdCovector, dotProduct, Fin.sum_univ_succ, map_div₀] at hb
  simp [Fin.sum_univ_succ, Derivation.leibniz, hcoord, map_add, map_mul, smul_eq_mul]
  field_simp [hr] at hb
  linear_combination hb

end DimensionFourDependence
