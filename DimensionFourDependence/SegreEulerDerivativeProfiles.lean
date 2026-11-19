import DimensionFourDependence.SegreRulingHomogeneousProfiles

/-! # Constructing the actual ruling profiles from Euler weights -/

namespace DimensionFourDependence

set_option maxHeartbeats 3000000

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

/-- The normalized ruling derivative is `x*partial_y`; its parameter
is the actual ratio `y/x` whenever the radial coordinate is constant
for `partial_y`. -/
theorem segre_radial_derivation_parameter
    (Dy : Derivation K F F) (x y : F) (hx : x ≠ 0) (hDx : Dy x = 0) (hDy : Dy y = 1) :
    (x • Dy) (y / x) = 1 := by
  simp only [Derivation.smul_apply, Derivation.leibniz_div, hDx, hDy, smul_eq_mul]
  field_simp <;> ring

/-- Differentiation of a normalized homogeneous function retains the
specified radial scale, including degree zero. -/
theorem segre_radial_normalized_derivative
    (Dy : Derivation K F F) (x f : F) (hx : x ≠ 0) (hDx : Dy x = 0) (k : ℕ) :
    (x • Dy) (f / x ^ k) = x * Dy f / x ^ k := by
  simp only [Derivation.smul_apply, Derivation.leibniz_div, Derivation.leibniz_pow,
    hDx, smul_eq_mul, mul_zero, nsmul_eq_mul, sub_zero]
  field_simp
  <;> ring

/-- A positive homogeneous degree constructs the normalized value and
both source partial derivatives in the exact radial frame. -/
theorem segre_euler_weight_constructs_function_profile
    (Dx Dy : Derivation K F F) (x y f : F) (hx : x ≠ 0) (hDyx : Dy x = 0)
    (k : ℕ) (hk : 0 < k) (heuler : x * Dx f + y * Dy f = (k : F) * f) :
    x * x ^ (k - 1) * (f / x ^ k) = f ∧
      x ^ (k - 1) * (x • Dy) (f / x ^ k) = Dy f ∧
      x ^ (k - 1) * ((k : F) * (f / x ^ k) - (y / x) * (x • Dy) (f / x ^ k)) = Dx f := by
  have hDx : Dx f = ((k : F) * f - y * Dy f) / x := by
    apply (eq_div_iff hx).mpr
    linear_combination heuler
  rw [segre_radial_normalized_derivative Dy x f hx hDyx k]
  rw [hDx]
  cases k with
  | zero => omega
  | succ n =>
    constructor
    · simp only [Nat.add_sub_cancel, pow_succ]
      field_simp
      <;> ring
    · constructor
      · simp only [Nat.add_sub_cancel, pow_succ]
        field_simp
        <;> ring
      · simp only [Nat.add_sub_cancel, pow_succ]
        field_simp
        <;> ring

/-- Euler weight minus one constructs the slope profile `A = x*a`
and both derivative values needed in the raw tangent matrix. -/
theorem segre_euler_weight_constructs_slope_profile
    (Dx Dy : Derivation K F F) (x y a : F) (hx : x ≠ 0) (hDyx : Dy x = 0)
    (heuler : x * Dx a + y * Dy a = -a) :
    (x * a) / x = a ∧
      (x • Dy) (x * a) / x ^ 2 = Dy a ∧
      (-(x * a) - (y / x) * (x • Dy) (x * a)) / x ^ 2 = Dx a := by
  have hDx : Dx a = (-a - y * Dy a) / x := by
    apply (eq_div_iff hx).mpr
    linear_combination heuler
  have hA : (x • Dy) (x * a) = x ^ 2 * Dy a := by
    simp only [Derivation.smul_apply, Derivation.leibniz, hDyx, smul_eq_mul, mul_zero, add_zero]
    ring
  rw [hA, hDx]
  constructor
  · field_simp
  · constructor
    · field_simp
    · field_simp
      <;> ring

/-- Dominance of the original homogeneous two-vector remains precisely
nonzero dominance of its normalized ruling profiles; no independent
Wronskian is imposed on newly chosen functions. -/
theorem segre_normalized_profile_wronskian_ne_zero
    (Dy : Derivation K F F) (x f g : F) (hx : x ≠ 0) (hDyx : Dy x = 0) (k : ℕ)
    (hdom : f * Dy g - g * Dy f ≠ 0) :
    (f / x ^ k) * (x • Dy) (g / x ^ k) -
      (g / x ^ k) * (x • Dy) (f / x ^ k) ≠ 0 := by
  rw [segre_radial_normalized_derivative Dy x g hx hDyx k,
    segre_radial_normalized_derivative Dy x f hx hDyx k]
  have he : f / x ^ k * (x * Dy g / x ^ k) - g / x ^ k * (x * Dy f / x ^ k) =
      (x / (x ^ k) ^ 2) * (f * Dy g - g * Dy f) := by
    field_simp
    <;> ring
  rw [he]
  exact mul_ne_zero (div_ne_zero hx (pow_ne_zero _ (pow_ne_zero k hx))) hdom

end DimensionFourDependence
