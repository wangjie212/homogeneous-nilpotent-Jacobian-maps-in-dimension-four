import DimensionFourDependence.SchemeRegularOrderBounds

/-! # Actual integer scheme orders in the pencil multiplicity identities -/

namespace DimensionFourDependence

open AlgebraicGeometry

variable {X : Scheme} [IsIntegral X] [IsLocallyNoetherian X]

/-- The unit rational function has actual integer order zero. -/
theorem scheme_integer_order_one (z : X) : X.ord (1 : X.functionField) z = 0 := by
  have h := Scheme.ord_mul (X := X) (x := z)
    (f := (1 : X.functionField)) (g := 1) one_ne_zero one_ne_zero
  simp only [one_mul] at h
  omega

/-- The actual integer order of a nonzero rational power is its
original order multiplied by the actual exponent. -/
theorem scheme_integer_order_pow (z : X) (f : X.functionField) (hf : f ≠ 0) (n : ℕ) :
    X.ord (f ^ n) z = (n : ℤ) * X.ord f z := by
  induction n with
  | zero => simp [scheme_integer_order_one]
  | succ n ih =>
    rw [pow_succ, Scheme.ord_mul (pow_ne_zero n hf) hf, ih]
    push_cast
    ring

/-- Every actual regular local coefficient has nonnegative integer
order at an intrinsic divisor DVR, including the zero coefficient. -/
theorem scheme_regular_integer_order_nonneg (z : X) (hz : Order.coheight z = 1)
    [IsDiscreteValuationRing (X.presheaf.stalk z)] (r : X.presheaf.stalk z) :
    0 ≤ X.ord (algebraMap (X.presheaf.stalk z) X.functionField r) z := by
  by_cases hr : r = 0
  · simp [hr, Scheme.ord_zero]
  · exact (scheme_regular_integer_order_bound_iff z hz r hr 0).mpr (by simp)

/-- A nonzero regular coefficient vanishes at the divisor precisely
when its actual integer order is at least one. -/
theorem scheme_regular_integer_order_positive_iff (z : X) (hz : Order.coheight z = 1)
    [IsDiscreteValuationRing (X.presheaf.stalk z)] (r : X.presheaf.stalk z) (hr : r ≠ 0) :
    1 ≤ X.ord (algebraMap (X.presheaf.stalk z) X.functionField r) z ↔
      r ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk z) := by
  simpa only [Nat.cast_one, pow_one] using scheme_regular_integer_order_bound_iff z hz r hr 1

/-- Actual regular unit transitions preserve the integer order of
every rational coefficient in every powered original frame. -/
theorem scheme_integer_order_powered_frame_eq
    {U : X.Opens} [Nonempty U] (z : X) (hz : z ∈ U)
    (t : Γ(X, U)) (ht : IsUnit t) (a b r : X.functionField)
    (ha : a ≠ 0) (hb : b ≠ 0) (hvalue : X.germToFunctionField U t = a / b) (n : ℕ) :
    X.ord (r / a ^ n) z = X.ord (r / b ^ n) z := by
  by_cases hr : r = 0
  · simp [hr, Scheme.ord_zero]
  have hbase : X.ord (a / b) z = 0 := hvalue ▸ Scheme.ord_of_isUnit ht hz
  have hpow : X.ord ((a / b) ^ n) z = 0 := by
    rw [scheme_integer_order_pow z _ (div_ne_zero ha hb), hbase, mul_zero]
  have heq : r / a ^ n * (a / b) ^ n = r / b ^ n := by
    rw [div_pow]
    field_simp
  have h := congrArg (fun f => X.ord f z) heq
  rw [Scheme.ord_mul (div_ne_zero hr (pow_ne_zero n ha))
    (pow_ne_zero n (div_ne_zero ha hb)), hpow, add_zero] at h
  exact h

/-- The original product-power equation computes the exact actual
order of its source-form coefficient. -/
theorem scheme_integer_order_product_eq_power
    (z : X) (u n r : X.functionField) (hr : r ≠ 0) (d : ℕ)
    (h : u * n = r ^ (d + 1)) :
    u ≠ 0 ∧ n ≠ 0 ∧ X.ord n z = ((d : ℤ) + 1) * X.ord r z - X.ord u z := by
  have hprod : u * n ≠ 0 := h ▸ pow_ne_zero (d + 1) hr
  have hu := (mul_ne_zero_iff.mp hprod).1
  have hn := (mul_ne_zero_iff.mp hprod).2
  have ho := congrArg (fun f => X.ord f z) h
  rw [Scheme.ord_mul hu hn, scheme_integer_order_pow z r hr] at ho
  push_cast at ho
  exact ⟨hu, hn, by omega⟩

/-- In the paper's product-power identity, a vanishing bounded
section and regular source coefficient force a vanishing root and the
original lower multiplicity estimates. -/
theorem scheme_integer_order_product_power_lower_bounds
    (z : X) (u n r : X.functionField) (hr : r ≠ 0) (d D : ℕ)
    (h : u * n = r ^ (d + 1))
    (hu : 1 ≤ X.ord u z) (huD : X.ord u z ≤ (D : ℤ))
    (hn : 0 ≤ X.ord n z) :
    1 ≤ X.ord r z ∧
      (d : ℤ) + 1 - D ≤ X.ord n z ∧ (d : ℤ) ≤ X.ord (r ^ d) z := by
  have heq := (scheme_integer_order_product_eq_power z u n r hr d h).2.2
  have hd : (0 : ℤ) ≤ d := Int.natCast_nonneg d
  have hroot : 1 ≤ X.ord r z := by
    by_contra! hroot
    have hle : X.ord r z ≤ 0 := by omega
    have hprod := mul_nonpos_of_nonneg_of_nonpos (by omega : (0 : ℤ) ≤ (d : ℤ) + 1) hle
    omega
  refine ⟨hroot, ?_, ?_⟩
  · nlinarith
  · rw [scheme_integer_order_pow z r hr]
    nlinarith

end DimensionFourDependence
