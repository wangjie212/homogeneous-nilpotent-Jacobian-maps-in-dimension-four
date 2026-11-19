import DimensionFourDependence.PolynomialCovectorProjectiveDescent
import DimensionFourDependence.IndependentParameterPolynomialDescent

/-! # The scaled normal power constructs a constant projected direction

At an independent parameter, a nonzero transverse point has nonzero
normal pairing. A scaled-power identity consequently forces both the
vertex coefficient and the remaining output value to be nonzero.
Algebraic parameter coefficients then construct the constant projected
direction, without assuming proportional tangent restrictions.
-/

namespace DimensionFourDependence

open Polynomial Matrix Module

set_option maxHeartbeats 2500000
set_option synthInstance.maxHeartbeats 100000

variable {K F L : Type*} [Field K] [IsAlgClosed K] [Field F] [Field L]
  [Algebra K F] [Algebra F L] [Algebra K L] [IsScalarTower K F L]

/-- The exact normal-power identity at an independent parameter
constructs a nonzero vertex coefficient, a nonzero output value and
a fixed original-field transverse direction. -/
theorem scaled_normal_power_constructs_constant_projected_direction
    (w : Fin 4 → RatFunc K) (v : Fin 4 → Polynomial K) (r : RatFunc K) (hr : r ≠ 0)
    (hLI : LinearIndependent (RatFunc K) (rationalParameterJetMatrix w).row)
    (hrep : ∀ i, w i = r * algebraMap (Polynomial K) (RatFunc K) (v i))
    (hvlast : v (Fin.last 3) = 0)
    (φ : RatFunc K →ₐ[K] L) (ht : Transcendental F (φ RatFunc.X))
    (x : Fin 3 → F) (hx : x ≠ 0) (h : F) (s a : L) (ha : a ≠ 0)
    (hcoeff : letI : Algebra (RatFunc K) L := φ.toRingHom.toAlgebra
      IsAlgebraic (RatFunc K) s ∧ IsAlgebraic (RatFunc K) a)
    (d : ℕ) (hd : 0 < d)
    (hpower : s * algebraMap F L h = a ^ d *
      (∑ i : Fin 3, φ (w i.castSucc) * algebraMap F L (x i)) ^ d) :
    s ≠ 0 ∧ h ≠ 0 ∧ ∃ (c : F) (b : Fin 3 → K), c ≠ 0 ∧ b ≠ 0 ∧
      x = c • (fun i => algebraMap K F (b i)) := by
  let t := φ RatFunc.X
  let P : Polynomial F := ∑ i : Fin 3, C (x i) * Polynomial.map (algebraMap K F) (v i.castSucc)
  have hdim := polynomial_normal_coefficient_kernel_finrank_le_one w v r hLI hrep
  have hP : P ≠ 0 := polynomial_covector_ternary_pairing_ne_zero v hdim hvlast x hx
  have hPt : Polynomial.aeval t P ≠ 0 := by
    intro hz
    apply hP
    exact transcendental_iff.mp ht P hz
  have hφr : φ r ≠ 0 := (_root_.map_ne_zero φ).mpr hr
  have hnormal : (∑ i : Fin 3, φ (w i.castSucc) * algebraMap F L (x i)) =
      φ r * Polynomial.aeval t P := by
    simp only [P, map_sum, map_mul, Polynomial.aeval_C,
      Polynomial.aeval_map_algebraMap F, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [hrep i.castSucc, map_mul, rational_function_algHom_polynomial_value]
    ring
  have hnormal0 : (∑ i : Fin 3, φ (w i.castSucc) * algebraMap F L (x i)) ≠ 0 := by
    rw [hnormal]
    exact mul_ne_zero hφr hPt
  have hleft : s * algebraMap F L h ≠ 0 := by
    rw [hpower]
    exact mul_ne_zero (pow_ne_zero d ha) (pow_ne_zero d hnormal0)
  have hs : s ≠ 0 := (mul_ne_zero_iff.mp hleft).1
  have hh : h ≠ 0 := (_root_.map_ne_zero (algebraMap F L)).mp (mul_ne_zero_iff.mp hleft).2
  let k : L := s / (a ^ d * (φ r) ^ d)
  have hden : a ^ d * (φ r) ^ d ≠ 0 := mul_ne_zero (pow_ne_zero d ha) (pow_ne_zero d hφr)
  have hpower' : (Polynomial.aeval t P) ^ d = k * algebraMap F L h := by
    apply (mul_left_cancel₀ hden)
    have he : (a ^ d * (φ r) ^ d) * (Polynomial.aeval t P) ^ d = s * algebraMap F L h := by
      rw [hpower, hnormal, mul_pow]
      ring
    calc
      (a ^ d * (φ r) ^ d) * (Polynomial.aeval t P) ^ d = s * algebraMap F L h := he
      _ = (a ^ d * (φ r) ^ d) * (k * algebraMap F L h) := by
        dsimp only [k]
        field_simp
  let : Algebra (RatFunc K) L := φ.toRingHom.toAlgebra
  have hk : IsAlgebraic (RatFunc K) k := by
    dsimp only [k]
    rw [div_eq_mul_inv]
    have hrAlg : IsAlgebraic (RatFunc K) (φ r) := by
      exact isAlgebraic_algebraMap r
    exact hcoeff.1.mul (((hcoeff.2.pow d).mul (hrAlg.pow d)).inv)
  obtain ⟨Q, hQ⟩ := independent_parameter_scaled_power_constructs_projective_polynomial
    φ t rfl ht P hP h hh d hd k hk hpower'
  obtain ⟨b, hb⟩ := polynomial_covector_projective_polynomial_descent_constructs_direction
    v hdim hvlast x P.leadingCoeff (leadingCoeff_ne_zero.mpr hP) Q hQ
  refine ⟨hs, hh, P.leadingCoeff, b, leadingCoeff_ne_zero.mpr hP, ?_, hb⟩
  intro hb0
  apply hx
  rw [hb, hb0]
  funext i
  simp only [Pi.smul_apply, Pi.zero_apply, map_zero, smul_eq_mul, mul_zero]

end DimensionFourDependence
