import DimensionFourDependence.DerivationSurfaceConstants
import DimensionFourDependence.CubicDifferentiation

/-! # The weighted affine-function calculation in (4.3)--(4.4)

A zero second directional derivative and Euler weight 1+1/d construct
a root of a transverse linear coordinate and a binary linear factor.
The coefficients are proved algebraic over the original ruling field.
The actual boundary incidence and its direction remain separate inputs.
-/

namespace DimensionFourDependence

universe u

variable {K F : Type u} [Field K] [Field F] [Algebra K F]

/-- Positive powers multiply derivation weights by their exponent. -/
theorem derivation_power_weight (D : Derivation K F F) (x w : F)
    (hx : D x = w * x) (n : ℕ) : D (x ^ n) = (n : F) * w * x ^ n := by
  rw [D.leibniz_pow, hx]
  simp only [smul_eq_mul, nsmul_eq_mul]
  by_cases hn : n = 0
  · subst n; simp
  · have hp : x ^ (n - 1) * x = x ^ n := by
      rw [← pow_succ, Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hn)]
    calc
      _ = (n : F) * w * (x ^ (n - 1) * x) := by ring
      _ = _ := by rw [hp]

/-- Quotients subtract derivation weights, also when the denominator is zero. -/
theorem derivation_quotient_weight (D : Derivation K F F) (x y v w : F)
    (hx : D x = v * x) (hy : D y = w * y) :
    D (x / y) = (v - w) * (x / y) := by
  by_cases hy0 : y = 0
  · simp [hy0]
  · rw [D.leibniz_div, hx, hy]
    simp only [smul_eq_mul]
    field_simp

variable [CharZero K]

/-- A transverse coordinate of weight one and a directional constant
of weight 1/d have a joint-constant dth-power quotient. -/
theorem weighted_root_power_quotient_joint_constant
    (D E : Derivation K F F) (s ρ : F) {d : ℕ} (hd : 0 < d)
    (hsD : D s = 0) (hsE : E s = s) (hρD : D ρ = 0)
    (hρE : E ρ = (d : F)⁻¹ * ρ) :
    D (ρ ^ d / s) = 0 ∧ E (ρ ^ d / s) = 0 := by
  let : CharZero F := charZero_of_injective_algebraMap (algebraMap K F).injective
  have hd0 : (d : F) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hd)
  have hpow : E (ρ ^ d) = ρ ^ d := by
    simpa only [mul_inv_cancel₀ hd0, one_mul] using derivation_power_weight E ρ _ hρE d
  constructor
  · rw [D.leibniz_div, D.leibniz_pow, hρD, hsD]
    simp
  · simpa using derivation_quotient_weight E (ρ ^ d) s 1 1 (by simpa using hpow) (by simpa using hsE)

/-- The field calculation behind (4.4), including the case of zero
directional slope. The root and all linear coefficients are constructed
inside the given field, and the coefficients are algebraic over its base.
No root or affine-factor presentation is assumed. -/
theorem weighted_affine_function_root_factorization
    (D E : Derivation K F F) (r s : F) (hrD : D r = 1) (hrE : E r = r)
    (hsD : D s = 0) (hsE : E s = s) (hs : s ≠ 0)
    (hcomm : ∀ x, D (E x) = E (D x) + D x)
    (htr : Algebra.trdeg K F ≤ 2) {d : ℕ} (hd : 0 < d)
    (f : F) (hf : f ≠ 0) (hsecond : D (D f) = 0)
    (hweight : E f = (1 + (d : F)⁻¹) * f) :
    ∃ α β γ ρ : F, IsAlgebraic K α ∧ IsAlgebraic K β ∧ IsAlgebraic K γ ∧
      α ≠ 0 ∧ ρ ≠ 0 ∧ f = (β * r + γ * s) * ρ ∧
      ρ ^ d = α * s ∧ D ρ = 0 ∧ (β ≠ 0 ∨ γ ≠ 0) := by
  let a := D f
  let b := f - r * a
  have haD : D a = 0 := hsecond
  have hbD : D b = 0 := by
    dsimp [b]
    rw [map_sub, D.leibniz, hrD, haD]
    simp [smul_eq_mul, a]
  have haE : E a = (d : F)⁻¹ * a := by
    have hwD : D (1 + (d : F)⁻¹) = 0 := by
      rw [map_add, D.map_one_eq_zero, derivation_inv_natCast_zero, zero_add]
    have he : E a + a = (1 + (d : F)⁻¹) * a := by
      calc
        _ = D (E f) := (hcomm f).symm
        _ = D ((1 + (d : F)⁻¹) * f) := congrArg D hweight
        _ = _ := by rw [D.leibniz, hwD, smul_zero, add_zero]; rfl
    linear_combination he
  have hbE : E b = (1 + (d : F)⁻¹) * b := by
    dsimp [b]
    rw [map_sub, E.leibniz, hrE, haE, hweight]
    simp only [smul_eq_mul]
    ring
  have hconst (x : F) (hxD : D x = 0) (hxE : E x = 0) : IsAlgebraic K x :=
    joint_direction_euler_constants_isAlgebraic D E r s hrD hsD hsE hs hcomm htr x hxD hxE
  by_cases ha : a = 0
  · let ρ := f / s
    have hρ : ρ ≠ 0 := div_ne_zero hf hs
    have hρD : D ρ = 0 := by
      apply (derivationConstants D).div_mem _ hsD
      exact ha
    have hρE : E ρ = (d : F)⁻¹ * ρ := by
      have he := derivation_quotient_weight E f s _ 1 hweight (by simpa using hsE)
      convert he using 1; ring
    obtain ⟨hαD, hαE⟩ := weighted_root_power_quotient_joint_constant D E s ρ hd hsD hsE hρD hρE
    refine ⟨ρ ^ d / s, 0, 1, ρ, hconst _ hαD hαE, ?_, ?_,
      div_ne_zero (pow_ne_zero d hρ) hs, hρ, ?_, ?_, hρD, Or.inr one_ne_zero⟩
    · exact isAlgebraic_zero
    · exact isAlgebraic_one
    · dsimp [ρ]; field_simp; ring
    · exact (div_mul_cancel₀ _ hs).symm
  · have hα := weighted_root_power_quotient_joint_constant D E s a hd hsD hsE haD haE
    have hprodE : E (s * a) = (1 + (d : F)⁻¹) * (s * a) := by
      rw [E.leibniz, hsE, haE]
      simp only [smul_eq_mul]
      ring
    have hγD : D (b / (s * a)) = 0 :=
      (derivationConstants D).div_mem hbD ((derivationConstants D).mul_mem hsD haD)
    have hγE : E (b / (s * a)) = 0 := by
      simpa using derivation_quotient_weight E b (s * a) _ _ hbE hprodE
    refine ⟨a ^ d / s, 1, b / (s * a), a, hconst _ hα.1 hα.2, isAlgebraic_one,
      hconst _ hγD hγE, div_ne_zero (pow_ne_zero d ha) hs, ha, ?_, ?_, haD, Or.inl one_ne_zero⟩
    · dsimp [b]
      field_simp
      ring
    · exact (div_mul_cancel₀ _ hs).symm

end DimensionFourDependence
