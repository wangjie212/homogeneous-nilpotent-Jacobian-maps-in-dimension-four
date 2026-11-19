import DimensionFourDependence.SegreQuadricHyperplaneRestriction
import DimensionFourDependence.PrimitiveBoundaryImage

/-! # Two ruling determinant identities force the two original constant hyperplanes to coincide -/

namespace DimensionFourDependence

open Polynomial Matrix

set_option maxHeartbeats 3000000

variable {K F : Type*} [Field K] [Field F]

/-- The actual quadratic determinant of two constant hyperplanes
restricted to the indicated ruling with its original rational parameter. -/
noncomputable def segreRulingHyperplaneDeterminant (j : Fin 3) (a l : Fin 4 → K) : Polynomial K :=
  Polynomial.C (a 0 * l (segreRulingRemainingIndex j).castSucc - a (segreRulingRemainingIndex j).castSucc * l 0) +
    Polynomial.C (a 0 * l 3 + a j.castSucc * l (segreRulingRemainingIndex j).castSucc -
      a (segreRulingRemainingIndex j).castSucc * l j.castSucc - a 3 * l 0) * Polynomial.X +
    Polynomial.C (a j.castSucc * l 3 - a 3 * l j.castSucc) * Polynomial.X ^ 2

/-- The determinant polynomial retains the exact restriction matrix
after any specified field embedding and parameter realization. -/
theorem segreRulingHyperplaneDeterminant_eval₂
    (φ : K →+* F) (j : Fin 3) (t : F) (a l : Fin 4 → K) :
    Polynomial.eval₂ φ t (segreRulingHyperplaneDeterminant j a l) =
      segreQuadricRulingBinaryCoefficients j t (fun i => φ (a i)) 0 *
        segreQuadricRulingBinaryCoefficients j t (fun i => φ (l i)) 1 -
      segreQuadricRulingBinaryCoefficients j t (fun i => φ (a i)) 1 *
        segreQuadricRulingBinaryCoefficients j t (fun i => φ (l i)) 0 := by
  simp [segreRulingHyperplaneDeterminant, segreQuadricRulingBinaryCoefficients,
    Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_pow,
    map_sub, map_add, map_mul]
  ring

/-- A nonzero common binary zero forces the actual determinant to vanish. -/
theorem binary_covectors_common_nonzero_zero_determinant
    (a l w : Fin 2 → F) (hw : w ≠ 0)
    (ha : a 0 * w 0 + a 1 * w 1 = 0) (hl : l 0 * w 0 + l 1 * w 1 = 0) :
    a 0 * l 1 - a 1 * l 0 = 0 := by
  by_cases hw0 : w 0 = 0
  · have hw1 : w 1 ≠ 0 := by
      intro hz
      apply hw
      funext i
      fin_cases i
      · exact hw0
      · exact hz
    apply (mul_eq_zero.mp (show (a 0 * l 1 - a 1 * l 0) * w 1 = 0 from by
      linear_combination a 0 * hl - l 0 * ha)).resolve_right hw1
  · apply (mul_eq_zero.mp (show (a 0 * l 1 - a 1 * l 0) * w 0 = 0 from by
      linear_combination l 1 * ha - a 1 * hl)).resolve_right hw0

/-- A nonzero ruling vector has a nonzero radial-varying coordinate pair. -/
theorem segre_ruling_kernel_radial_varying_pair_ne_zero
    (j : Fin 3) (hj : j ≠ 0) (t : F) (v : Fin 4 → F) (hv : v ≠ 0)
    (hkernel : segreRulingMatrix j t *ᵥ v = 0) :
    (![v 0, v (segreRulingRemainingIndex j).castSucc] : Fin 2 → F) ≠ 0 := by
  intro hz
  have h0 : v 0 = 0 := congrFun hz 0
  have hother : v (segreRulingRemainingIndex j).castSucc = 0 := congrFun hz 1
  have hk0 := congrFun hkernel 0
  have hk1 := congrFun hkernel 1
  rw [segreRulingMatrix_mulVec] at hk0 hk1
  apply hv
  fin_cases j
  · exact False.elim (hj rfl)
  · change v 2 = 0 at hother
    have h1 : v 1 = 0 := by simpa [h0] using hk0
    have h3 : v 3 = 0 := by simpa [hother] using hk1
    funext i
    fin_cases i <;> assumption
  · change v 1 = 0 at hother
    have h2 : v 2 = 0 := by simpa [h0] using hk0
    have h3 : v 3 = 0 := by simpa [hother] using hk1
    funext i
    fin_cases i <;> assumption

variable [CharZero K]

/-- Vanishing of the two original ruling determinant polynomials makes
all six cross minors zero, so the two nonzero original covectors are
proportional over the original field. This is the quadric fixed-line
argument in direct original coordinates. -/
theorem two_segre_ruling_hyperplane_determinants_zero_covectors_proportional
    (a l : Fin 4 → K) (ha : a ≠ 0) (hl : l ≠ 0)
    (hfirst : segreRulingHyperplaneDeterminant 2 a l = 0)
    (hsecond : segreRulingHyperplaneDeterminant 1 a l = 0) :
    ∃ α : K, α ≠ 0 ∧ ∀ i, l i = α * a i := by
  have h01 := congrArg (fun P : Polynomial K => P.coeff 0) hfirst
  have h23 := congrArg (fun P : Polynomial K => P.coeff 2) hfirst
  have hm1 := congrArg (fun P : Polynomial K => P.coeff 1) hfirst
  have h02 := congrArg (fun P : Polynomial K => P.coeff 0) hsecond
  have h13 := congrArg (fun P : Polynomial K => P.coeff 2) hsecond
  have hm2 := congrArg (fun P : Polynomial K => P.coeff 1) hsecond
  simp only [segreRulingHyperplaneDeterminant, Polynomial.coeff_add, Polynomial.coeff_C_mul,
    Polynomial.coeff_C, Polynomial.coeff_X, Polynomial.coeff_X_pow,
    Polynomial.coeff_zero] at h01 h23 hm1 h02 h13 hm2
  simp [segreRulingRemainingIndex] at h01 h23 hm1 h02 h13 hm2
  have h03 : a 0 * l 3 - a 3 * l 0 = 0 := by linear_combination (1 / 2 : K) * hm1 + (1 / 2 : K) * hm2
  have h12 : a 1 * l 2 - a 2 * l 1 = 0 := by linear_combination (1 / 2 : K) * hm2 - (1 / 2 : K) * hm1
  have h10 : a 1 * l 0 - a 0 * l 1 = 0 := by linear_combination -h01
  have h20 : a 2 * l 0 - a 0 * l 2 = 0 := by linear_combination -h02
  have h30 : a 3 * l 0 - a 0 * l 3 = 0 := by linear_combination -h03
  have h21 : a 2 * l 1 - a 1 * l 2 = 0 := by linear_combination -h12
  have h31 : a 3 * l 1 - a 1 * l 3 = 0 := by linear_combination -h13
  have h32 : a 3 * l 2 - a 2 * l 3 = 0 := by linear_combination -h23
  apply nonzero_vectors_proportional_of_cross_equations a l ha hl
  intro i j
  fin_cases i <;> fin_cases j <;>
    first | exact h01 | exact h02 | exact h03 | exact h10 | exact h12 | exact h13 |
      exact h20 | exact h21 | exact h23 | exact h30 | exact h31 | exact h32 | ring

end DimensionFourDependence
