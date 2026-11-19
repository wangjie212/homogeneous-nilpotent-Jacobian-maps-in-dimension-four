import DimensionFourDependence.PolynomialDivergence

/-! # The Taylor congruence in Section 3.1 after clearing a coordinate denominator -/

namespace DimensionFourDependence

open MvPolynomial

variable {K : Type*} [Field K]

/-- The first-order Taylor identity forces `grad R · W = -f` modulo
the image equation, with no localization or rational-function remainder. -/
theorem radial_taylor_gradient_congruence
    (R f q : MvPolynomial (Fin 4) K) {n : ℕ} (hn : 0 < n)
    (hRh : R.IsHomogeneous n) (hR : Irreducible R) (hf : ¬ R ∣ f)
    (V W : Fin 4 → MvPolynomial (Fin 4) K) (hV : aeval V R = 0)
    (hpoint : (fun i => q * V i) = fun i => f * X i + R * W i) :
    R ∣ polynomialGradientPairing R W + f := by
  obtain ⟨T, hT⟩ := first_order_taylor_square_remainder
    (fun i : Fin 4 => f * X i) W R R
  rw [homogeneous_aeval_scaled_coordinates R hRh f,
    homogeneous_directional_differential_scaled_coordinates R hRh f W] at hT
  change aeval (fun i => f * X i + R * W i) R =
    f ^ n * R + R * (f ^ (n - 1) * polynomialGradientPairing R W) + R ^ 2 * T at hT
  have hz : aeval (fun i => f * X i + R * W i) R = 0 := by
    rw [← hpoint, homogeneous_aeval_scale R hRh V q, hV, mul_zero]
  rw [hz] at hT
  have hpow : f ^ n = f ^ (n - 1) * f := by
    conv_lhs => rw [show n = (n - 1) + 1 by omega, pow_succ]
  rw [hpow] at hT
  have hfactor : R * (f ^ (n - 1) * (f + polynomialGradientPairing R W) + R * T) = 0 := by
    linear_combination -hT
  have hinner := (mul_eq_zero.mp hfactor).resolve_left hR.ne_zero
  have hdiv : R ∣ f ^ (n - 1) * (f + polynomialGradientPairing R W) := by
    refine ⟨-T, ?_⟩
    linear_combination hinner
  have hnot : ¬ R ∣ f ^ (n - 1) := fun h => hf (hR.prime.dvd_of_dvd_pow h)
  have hh := (hR.prime.dvd_or_dvd hdiv).resolve_left hnot
  simpa only [add_comm] using hh

/-- Dividing a common power from a map preserves its homogeneous image equation. -/
theorem homogeneous_relation_remove_common_power
    (R : MvPolynomial (Fin 4) K) {n : ℕ} (hR0 : R ≠ 0) (hRh : R.IsHomogeneous n)
    (H V : Fin 4 → MvPolynomial (Fin 4) K) (m : ℕ)
    (hH : H = fun i => R ^ m * V i) (hzero : aeval H R = 0) : aeval V R = 0 := by
  rw [hH, homogeneous_aeval_scale R hRh V (R ^ m)] at hzero
  exact (mul_eq_zero.mp hzero).resolve_left (pow_ne_zero n (pow_ne_zero m hR0))

end DimensionFourDependence
