import DimensionFourDependence.BivariateBilinearCoefficients
import DimensionFourDependence.BivariateAlgebraicRulingFactors
import DimensionFourDependence.SegreCommonFieldBivariateDescent

/-! # Global bilinear factors are original constant hyperplane forms on the Segre quadric -/

namespace DimensionFourDependence

open Polynomial Matrix

set_option maxHeartbeats 3000000

variable {K E : Type*} [Field K] [Field E] [Algebra K E]

/-- The four actual coefficients of a bilinear chart polynomial,
in the original Segre coordinate order 1,s,t,st. -/
noncomputable def segreBilinearCovector (P : Polynomial (Polynomial K)) : Fin 4 → K :=
  ![(P.coeff 0).coeff 0, (P.coeff 1).coeff 0, (P.coeff 0).coeff 1, (P.coeff 1).coeff 1]

/-- A nonzero global bilinear polynomial gives a nonzero original
constant hyperplane covector. -/
theorem segre_bilinear_covector_ne_zero
    (P : Polynomial (Polynomial K)) (hP : BivariateBilinear P) (hP0 : P ≠ 0) :
    segreBilinearCovector P ≠ 0 := by
  intro h
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  have h2 := congrFun h 2
  have h3 := congrFun h 3
  change (P.coeff 0).coeff 0 = 0 at h0
  change (P.coeff 1).coeff 0 = 0 at h1
  change (P.coeff 0).coeff 1 = 0 at h2
  change (P.coeff 1).coeff 1 = 0 at h3
  apply hP0
  rw [bivariate_bilinear_four_term_normal_form P hP, h0, h1, h2, h3]
  simp

/-- The bilinear chart polynomial is exactly its constant hyperplane
form divided by the original radial coordinate on the original quadric. -/
theorem segre_bilinear_polynomial_hyperplane_value
    (P : Polynomial (Polynomial K)) (hP : BivariateBilinear P)
    (Y : Fin 4 → E) (hY0 : Y 0 ≠ 0) (hSegre : Y 0 * Y 3 - Y 1 * Y 2 = 0) :
    ((fun i => algebraMap K E (segreBilinearCovector P i)) ⬝ᵥ Y) / Y 0 =
      Polynomial.eval₂ (Polynomial.aeval (Y 2 / Y 0)).toRingHom (Y 1 / Y 0) P := by
  conv_rhs => rw [bivariate_bilinear_four_term_normal_form P hP]
  simp [segreBilinearCovector, dotProduct, Fin.sum_univ_succ,
    Polynomial.eval₂_add, Polynomial.eval₂_mul]
  field_simp [hY0]
  linear_combination (algebraMap K E ((P.coeff 1).coeff 1)) * hSegre

/-- The global chart power factorization is exactly the original
homogeneous radial-product identity (5.3), with two nonzero original
constant hyperplane covectors constructed from the actual factors. -/
theorem segre_bilinear_power_factorization_constructs_radial_hyperplane_identity
    (P R B : Polynomial (Polynomial K)) (hR : BivariateBilinear R) (hB : BivariateBilinear B)
    (hR0 : R ≠ 0) (hB0 : B ≠ 0) (Y : Fin 4 → E) (hY0 : Y 0 ≠ 0)
    (hSegre : Y 0 * Y 3 - Y 1 * Y 2 = 0) (f : E) (d : ℕ)
    (hvalue : f ^ d / Y 0 ^ (d + 1) =
      Polynomial.eval₂ (Polynomial.aeval (Y 2 / Y 0)).toRingHom (Y 1 / Y 0) P)
    (hfactor : P = R * B ^ d) :
    ∃ r b : Fin 4 → K, r ≠ 0 ∧ b ≠ 0 ∧
      f ^ d = ((fun i => algebraMap K E (r i)) ⬝ᵥ Y) *
        ((fun i => algebraMap K E (b i)) ⬝ᵥ Y) ^ d := by
  refine ⟨segreBilinearCovector R, segreBilinearCovector B,
    segre_bilinear_covector_ne_zero R hR hR0, segre_bilinear_covector_ne_zero B hB hB0, ?_⟩
  rw [hfactor, Polynomial.eval₂_mul, Polynomial.eval₂_pow,
    ← segre_bilinear_polynomial_hyperplane_value R hR Y hY0 hSegre,
    ← segre_bilinear_polynomial_hyperplane_value B hB Y hY0 hSegre] at hvalue
  have hden : Y 0 ^ (d + 1) ≠ 0 := pow_ne_zero _ hY0
  apply (div_left_inj' hden).mp
  calc
    _ = _ := hvalue
    _ = _ := by rw [div_pow, pow_succ]; field_simp [hY0]

end DimensionFourDependence
