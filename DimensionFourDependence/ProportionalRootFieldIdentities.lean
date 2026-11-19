import DimensionFourDependence.RulingRootProductIdentity

/-! # The exact field identities in the two remaining root cases -/

namespace DimensionFourDependence

variable {F : Type*} [Field F]

/-- A denominator proportional to the original numerator makes the
actual root a nonzero-parameter scalar multiple of the input form. -/
theorem rational_root_of_proportional_denominator
    (r m n L γ : F) (hγ : γ ≠ 0) (hn : n ≠ 0) (hm : m = γ * n)
    (hformula : r = n * L / m) : r = γ⁻¹ * L := by
  rw [hformula, hm]
  field_simp [hγ, hn]

/-- If the root power is proportional to the numerator, the
original numerator and denominator have the exact degree-d and
degree-(d-1) factorizations used in (4.6). -/
theorem rational_root_of_proportional_power_values
    (r m n s L β : F) {d : ℕ} (hd : 0 < d) (hr : r ≠ 0) (hβ : β ≠ 0) (hm : m ≠ 0)
    (hroot : r ^ d = s) (hs : s = β * n) (hformula : r = n * L / m) :
    n = β⁻¹ * r ^ d ∧ m = β⁻¹ * r ^ (d - 1) * L := by
  have hn : n = β⁻¹ * r ^ d := by
    rw [hroot, hs]
    field_simp [hβ]
  have hcompat : m * r = n * L := (mul_comm m r).trans ((eq_div_iff hm).mp hformula)
  have hpow : r ^ d = r ^ (d - 1) * r := by
    rw [← pow_succ]
    congr 1
    omega
  refine ⟨hn, ?_⟩
  apply mul_right_cancel₀ hr
  rw [hcompat, hn, hpow]
  ring

end DimensionFourDependence
