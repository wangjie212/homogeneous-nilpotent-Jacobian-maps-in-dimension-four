import DimensionFourDependence.WeightedRulingCoordinates
import DimensionFourDependence.GraphNormalSecondJet

/-! # The simple fixed root in the binary Hessian of Section 4.3

The weighted function (a r + c s) rho, with rho^d = s, has a
factorized directional Hessian. When a is nonzero and d > 1, its two
projective roots are distinct. A direction algebraic over the parameter
cannot be the varying root: differentiating in the longitudinal
coordinate forces its transverse coordinate to vanish.

These are field and differential statements. The local intersection
length and the geometric degree bound for the fiber curve are separate.
-/

namespace DimensionFourDependence

variable {K F : Type*} [Field K] [Field F] [Algebra K F] [CharZero F]

/-- Differentiating the actual root equation gives its logarithmic
derivative, without an independently supplied derivative of the root. -/
theorem linear_coordinate_root_derivative
    (D : Derivation K F F) {d : ℕ} (hd : 0 < d)
    (rho s : F) (hrho : rho ≠ 0) (hroot : rho ^ d = s) :
    D rho = (d : F)⁻¹ * rho / s * D s := by
  have hd0 : (d : F) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hd)
  have hs : s ≠ 0 := hroot ▸ pow_ne_zero d hrho
  have hp : rho ^ (d - 1) * rho = rho ^ d := by
    rw [← pow_succ, Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hd))]
  have he := congrArg D hroot
  rw [D.leibniz_pow] at he
  simp only [smul_eq_mul, nsmul_eq_mul] at he
  have he' : ((d : F) * s) * D rho = rho * D s := by
    calc
      _ = ((d : F) * (rho ^ (d - 1) * D rho)) * rho := by rw [← hroot, ← hp]; ring
      _ = D s * rho := by rw [he]
      _ = _ := by ring
  apply mul_left_cancel₀ (mul_ne_zero hd0 hs)
  rw [he']
  field_simp

/-- The second derivative of a root of a linear coordinate. -/
theorem linear_coordinate_root_second_derivative
    (D : Derivation K F F) {d : ℕ} (hd : 0 < d)
    (rho s v : F) (hrho : rho ≠ 0) (hroot : rho ^ d = s)
    (hs : D s = v) (hv : D v = 0) :
    D (D rho) = (d : F)⁻¹ * ((d : F)⁻¹ - 1) * rho / s ^ 2 * v ^ 2 := by
  have hs0 : s ≠ 0 := hroot ▸ pow_ne_zero d hrho
  have hd0 : (d : F) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hd)
  have he : D rho = (d : F)⁻¹ * rho / s * v := by
    rw [linear_coordinate_root_derivative D hd rho s hrho hroot, hs]
  rw [he, D.leibniz, hv]
  simp only [smul_eq_mul, mul_zero, zero_add]
  rw [D.leibniz_div, D.leibniz, derivation_inv_natCast_zero, hs, he]
  simp only [smul_eq_mul, mul_zero, add_zero]
  field_simp [hs0, hd0]

/-- The exact factorization of the binary Hessian in Section 4.3,
with its root derivatives derived from rho^d=s. -/
theorem simple_fixed_root_directional_hessian
    (D : Derivation K F F) {d : ℕ} (hd : 0 < d)
    (r s rho a c u v : F) (hrho : rho ≠ 0) (hroot : rho ^ d = s)
    (hr : D r = u) (hs : D s = v)
    (ha : D a = 0) (hc : D c = 0) (hu : D u = 0) (hv : D v = 0) :
    D (D ((a * r + c * s) * rho)) =
      ((d : F)⁻¹ * rho / s ^ 2) * v *
        (2 * a * s * u + (((d : F)⁻¹ - 1) * a * r + ((d : F)⁻¹ + 1) * c * s) * v) := by
  have hm : D (a * r + c * s) = a * u + c * v := by
    simp only [map_add, D.leibniz, ha, hc, hr, hs, smul_eq_mul, mul_zero, add_zero]
  have hmm : D (D (a * r + c * s)) = 0 := by
    rw [hm]
    simp only [map_add, D.leibniz, ha, hc, hu, hv, smul_eq_mul, mul_zero, add_zero]
  have hs0 : s ≠ 0 := hroot ▸ pow_ne_zero d hrho
  rw [derivation_second_product, hmm, hm,
    linear_coordinate_root_second_derivative D hd rho s v hrho hroot hs hv,
    linear_coordinate_root_derivative D hd rho s hrho hroot, hs]
  field_simp
  ring

/-- The nonzero scalar in the Hessian does not affect its roots. -/
theorem simple_fixed_root_hessian_zero_iff
    (D : Derivation K F F) {d : ℕ} (hd : 0 < d)
    (r s rho a c u v : F) (hrho : rho ≠ 0) (hroot : rho ^ d = s)
    (hr : D r = u) (hs : D s = v)
    (ha : D a = 0) (hc : D c = 0) (hu : D u = 0) (hv : D v = 0) :
    D (D ((a * r + c * s) * rho)) = 0 ↔
      v = 0 ∨ 2 * a * s * u +
        (((d : F)⁻¹ - 1) * a * r + ((d : F)⁻¹ + 1) * c * s) * v = 0 := by
  rw [simple_fixed_root_directional_hessian D hd r s rho a c u v hrho hroot hr hs ha hc hu hv]
  have hscalar : (d : F)⁻¹ * rho / s ^ 2 ≠ 0 :=
    div_ne_zero (mul_ne_zero (inv_ne_zero (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hd))) hrho)
      (pow_ne_zero 2 (hroot ▸ pow_ne_zero d hrho))
  rw [mul_assoc, mul_eq_zero, or_iff_right (by exact hscalar), mul_eq_zero]

/-- The linear factor is nonzero at the fixed projective root [1:0].
Thus the two linear factors have distinct projective zeros. -/
theorem simple_fixed_root_linear_factor_at_fixed_direction
    {d : ℕ} (r s a c : F) (ha : a ≠ 0) (hs : s ≠ 0) :
    2 * a * s * (1 : F) +
      (((d : F)⁻¹ - 1) * a * r + ((d : F)⁻¹ + 1) * c * s) * 0 ≠ 0 := by
  simpa using mul_ne_zero (mul_ne_zero (by norm_num : (2 : F) ≠ 0) ha) hs

/-- For d>1 the longitudinal coefficient of the moving root is nonzero. -/
theorem inverse_natCast_sub_one_ne_zero {d : ℕ} (hd : 1 < d) :
    (d : F)⁻¹ - 1 ≠ 0 := by
  have hd0 : (d : F) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  intro he
  have hi : (d : F)⁻¹ = 1 := sub_eq_zero.mp he
  have he' := congrArg (fun z : F => z * (d : F)) hi
  rw [inv_mul_cancel₀ hd0, one_mul] at he'
  have hd1 : d = 1 := by exact_mod_cast he'.symm
  omega

/-- A direction constant in the longitudinal coordinate cannot equal
the varying Hessian root. No varying-root exclusion is a hypothesis. -/
theorem longitudinal_constant_simple_fixed_root_direction
    (R : Derivation K F F) {d : ℕ} (hd : 1 < d)
    (r s a c u v : F) (ha0 : a ≠ 0)
    (hr : R r = 1) (hs : R s = 0)
    (ha : R a = 0) (hc : R c = 0) (hu : R u = 0) (hv : R v = 0)
    (hzero : v * (2 * a * s * u +
      (((d : F)⁻¹ - 1) * a * r + ((d : F)⁻¹ + 1) * c * s) * v) = 0) :
    v = 0 := by
  have he := congrArg R hzero
  have htwo : R (2 : F) = 0 := R.map_natCast 2
  simp only [R.map_zero, R.leibniz, map_add, map_sub, R.map_one_eq_zero,
    derivation_inv_natCast_zero, htwo, hr, hs, ha, hc, hu, hv,
    smul_eq_mul, mul_zero, mul_one, add_zero, sub_zero] at he
  have he' : (((d : F)⁻¹ - 1) * a) * v ^ 2 = 0 := by
    linear_combination he
  have hn := mul_ne_zero (inverse_natCast_sub_one_ne_zero (F := F) hd) ha0
  exact (pow_eq_zero_iff'.mp ((mul_eq_zero.mp he').resolve_left hn)).1

variable [CharZero K]

/-- The actual parameter-algebraicity condition excludes the moving
root by derivation, without a supplied nonconstancy argument. -/
theorem parameter_algebraic_simple_fixed_root_direction
    (p : RatFunc K →ₐ[K] F) (R : Derivation K F F)
    (ht : R (p RatFunc.X) = 0) {d : ℕ} (hd : 1 < d)
    (r s a c u v : F) (ha0 : a ≠ 0) (hr : R r = 1) (hs : R s = 0)
    (ha : IsAlgebraic p.fieldRange a) (hc : IsAlgebraic p.fieldRange c)
    (hu : IsAlgebraic p.fieldRange u) (hv : IsAlgebraic p.fieldRange v)
    (hzero : v * (2 * a * s * u +
      (((d : F)⁻¹ - 1) * a * r + ((d : F)⁻¹ + 1) * c * s) * v) = 0) :
    v = 0 :=
  longitudinal_constant_simple_fixed_root_direction R hd r s a c u v ha0 hr hs
    (parameter_algebraic_coefficient_direction_constant p R ht a ha)
    (parameter_algebraic_coefficient_direction_constant p R ht c hc)
    (parameter_algebraic_coefficient_direction_constant p R ht u hu)
    (parameter_algebraic_coefficient_direction_constant p R ht v hv) hzero

/-- A parameter-algebraic direction with zero second derivative of
the actual weighted function must annihilate the transverse root form.
All root and direction derivatives follow from the original equations. -/
theorem parameter_algebraic_zero_acceleration_has_fixed_root
    (p : RatFunc K →ₐ[K] F) (D R : Derivation K F F)
    (htD : D (p RatFunc.X) = 0) (htR : R (p RatFunc.X) = 0)
    {d : ℕ} (hd : 1 < d) (r s rho a c : F)
    (hrho : rho ≠ 0) (hroot : rho ^ d = s) (ha0 : a ≠ 0)
    (hr : R r = 1) (hs : R s = 0)
    (ha : IsAlgebraic p.fieldRange a) (hc : IsAlgebraic p.fieldRange c)
    (hu : IsAlgebraic p.fieldRange (D r)) (hv : IsAlgebraic p.fieldRange (D s))
    (hsecond : D (D ((a * r + c * s) * rho)) = 0) :
    D s = 0 := by
  have hdir := (simple_fixed_root_hessian_zero_iff D (by omega) r s rho a c (D r) (D s)
    hrho hroot rfl rfl
    (parameter_algebraic_coefficient_direction_constant p D htD a ha)
    (parameter_algebraic_coefficient_direction_constant p D htD c hc)
    (parameter_algebraic_coefficient_direction_constant p D htD (D r) hu)
    (parameter_algebraic_coefficient_direction_constant p D htD (D s) hv)).mp hsecond
  apply parameter_algebraic_simple_fixed_root_direction p R htR hd r s a c (D r) (D s)
    ha0 hr hs ha hc hu hv
  rcases hdir with hz | hz <;> rw [hz] <;> ring

end DimensionFourDependence
