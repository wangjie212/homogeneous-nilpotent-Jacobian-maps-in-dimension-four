import DimensionFourDependence.ParametricWeightedRulingFactorization

/-! # A stationary ruling function of weight 2/d has a square linear-form dth power -/

namespace DimensionFourDependence

universe u
set_option maxHeartbeats 2500000

variable {K F : Type u} [Field K] [CharZero K] [Field F] [Algebra K F]

/-- A nonzero stationary function of weight 2/d constructs its actual
nonzero scalar square quotient. Joint directional-Euler constants are
proved algebraic over the original ruling field. -/
theorem stationary_weight_two_power_constructs_algebraic_square_scalar
    (D E : Derivation K F F) (r s : F) (hrD : D r = 1)
    (hsD : D s = 0) (hsE : E s = s) (hs : s ≠ 0)
    (hcomm : ∀ x, D (E x) = E (D x) + D x)
    (htr : Algebra.trdeg K F ≤ 2) (d : ℕ) (hd : 0 < d)
    (f : F) (hf : f ≠ 0) (hDf : D f = 0)
    (hweight : E f = (2 * (d : F)⁻¹) * f) :
    ∃ α : F, IsAlgebraic K α ∧ α ≠ 0 ∧ f ^ d = α * s ^ 2 := by
  letI : CharZero F := charZero_of_injective_algebraMap (algebraMap K F).injective
  have hd0 : (d : F) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hnumD : D (f ^ d) = 0 := by rw [D.leibniz_pow, hDf]; simp
  have hdenD : D (s ^ 2) = 0 := by rw [D.leibniz_pow, hsD]; simp
  have hnumE : E (f ^ d) = 2 * f ^ d := by
    have he := derivation_power_weight E f _ hweight d
    convert he using 1
    field_simp [hd0]
  have hdenE : E (s ^ 2) = 2 * s ^ 2 := by
    simpa only [Nat.cast_ofNat, mul_one] using derivation_power_weight E s 1 (by simpa using hsE) 2
  let α := f ^ d / s ^ 2
  have hαD : D α = 0 := by
    exact (derivationConstants D).div_mem hnumD hdenD
  have hαE : E α = 0 := by
    simpa only [sub_self, zero_mul] using derivation_quotient_weight E (f ^ d) (s ^ 2) 2 2 hnumE hdenE
  have hαalg := joint_direction_euler_constants_isAlgebraic D E r s hrD hsD hsE hs hcomm htr α hαD hαE
  exact ⟨α, hαalg, div_ne_zero (pow_ne_zero d hf) (pow_ne_zero 2 hs),
    (div_mul_cancel₀ _ (pow_ne_zero 2 hs)).symm⟩

end DimensionFourDependence
