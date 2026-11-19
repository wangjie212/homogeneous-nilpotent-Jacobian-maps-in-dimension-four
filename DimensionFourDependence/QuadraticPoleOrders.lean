import DimensionFourDependence.CurvePoleValuation

/-! # Pole comparisons from the quadratic fiber normal form

These are the two valuation comparisons used in Section 3.2: simultaneous
isotropic-coordinate poles force a strictly dominant radial coordinate
when the radial coefficient is nonzero; hyperbola poles are separated.
-/

namespace DimensionFourDependence

variable {E F Γ : Type*} [Field E] [Field F] [Algebra E F]
    [LinearOrderedCommGroupWithZero Γ] (v : Valuation F Γ) [hv : v.IsTrivialOn E]

/-- In (3.3), simultaneous poles of `s,t` give radial value exactly
`v(s)v(t)`, strictly greater than both isotropic values and one. -/
theorem quadratic_normal_form_simultaneous_poles
    (a α β κ q : E) (ha : a ≠ 0) (hκ : κ ≠ 0) (τ s t : F)
    (heq : algebraMap E F q = algebraMap E F a * τ + algebraMap E F α * s +
      algebraMap E F β * t + algebraMap E F κ * s * t)
    (hs : 1 < v s) (ht : 1 < v t) :
    v τ = v s * v t ∧ v s < v τ ∧ v t < v τ ∧ 1 < v τ := by
  have hc (b : E) : v (algebraMap E F b) ≤ 1 := by
    by_cases hb : b = 0
    · simp only [hb, map_zero, zero_le_one]
    · rw [hv.eq_one b hb]
  have hvs : v s < v s * v t := by
    simpa only [mul_one] using mul_lt_mul_of_pos_left ht (zero_lt_one.trans hs)
  have hvt : v t < v s * v t := by
    simpa only [one_mul] using mul_lt_mul_of_pos_right hs (zero_lt_one.trans ht)
  have hone : 1 < v s * v t := hs.trans hvs
  have hα : v (algebraMap E F α * s) < v s * v t := by
    rw [map_mul]
    exact (mul_le_mul_of_nonneg_right (hc α) (zero_lt_one.trans hs).le).trans_lt
      (by simpa only [one_mul] using hvs)
  have hβ : v (algebraMap E F β * t) < v s * v t := by
    rw [map_mul]
    exact (mul_le_mul_of_nonneg_right (hc β) (zero_lt_one.trans ht).le).trans_lt
      (by simpa only [one_mul] using hvt)
  have hbase : v (algebraMap E F q - algebraMap E F α * s - algebraMap E F β * t) < v s * v t :=
    v.map_sub_lt (v.map_sub_lt ((hc q).trans_lt hone) hα) hβ
  have hproduct : v (algebraMap E F κ * s * t) = v s * v t := by
    rw [map_mul, map_mul, hv.eq_one κ hκ, one_mul]
  have he : algebraMap E F a * τ =
      (algebraMap E F q - algebraMap E F α * s - algebraMap E F β * t) - algebraMap E F κ * s * t := by
    linear_combination -heq
  have hτ : v τ = v s * v t := by
    calc
      v τ = v (algebraMap E F a * τ) := by rw [map_mul, hv.eq_one a ha, one_mul]
      _ = v ((algebraMap E F q - algebraMap E F α * s - algebraMap E F β * t) -
          algebraMap E F κ * s * t) := congrArg v he
      _ = v (algebraMap E F κ * s * t) := v.map_sub_eq_of_lt_right (by rw [hproduct]; exact hbase)
      _ = v s * v t := hproduct
  exact ⟨hτ, by simpa only [hτ] using hvs, by simpa only [hτ] using hvt, by simpa only [hτ] using hone⟩

/-- On `q=kappa*s*t` with nonzero constant `q,kappa`, the other
coordinate has value less than one at every pole of one coordinate. -/
theorem hyperbola_poles_separated
    (κ q : E) (hκ : κ ≠ 0) (hq : q ≠ 0) (s t : F)
    (heq : algebraMap E F q = algebraMap E F κ * s * t) (hs : 1 < v s) : v t < 1 := by
  have hprod : v s * v t = 1 := by
    have he := congrArg v heq
    simpa only [map_mul, hv.eq_one q hq, hv.eq_one κ hκ, one_mul] using he.symm
  have hs0 : v s ≠ 0 := ne_of_gt (zero_lt_one.trans hs)
  have ht : v t = (v s)⁻¹ := by
    apply mul_left_cancel₀ hs0
    rw [mul_inv_cancel₀ hs0]
    exact hprod
  rw [ht]
  exact inv_lt_one_of_one_lt₀ hs

end DimensionFourDependence
