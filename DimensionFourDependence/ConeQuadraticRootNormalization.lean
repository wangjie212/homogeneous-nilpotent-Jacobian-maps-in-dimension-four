import DimensionFourDependence.ConeQuadraticCoefficient

/-! # A nonzero algebraic quadratic coefficient is absorbed in the cone root

Replacing r by r/kappa turns C = kappa/r into C = 1/r_new. The original
four cone formulas retain their form after multiplying their parameter
coefficients by the appropriate powers of kappa. These new coefficients
are still parameter-algebraic and the last coefficient remains nonzero.
-/

namespace DimensionFourDependence

set_option maxHeartbeats 2000000

variable {F : Type*} [Field F]

/-- Rescaling the root preserves the complete cone expression and
normalizes its nonzero quadratic coefficient to a unit numerator. -/
theorem cone_root_rescaling_normalizes_quadratic_coefficient
    (r κ C a b L : F) (V : Fin 3 → F) (d : ℕ) (hr : r ≠ 0) (hκ : κ ≠ 0)
    (hC : C = κ / r) :
    r / κ ≠ 0 ∧ C = 1 / (r / κ) ∧
      (∀ i : Fin 3, V i * r ^ d = (V i * κ ^ d) * (r / κ) ^ d) ∧
      a * r ^ d + b * r ^ (d - 1) * L =
        (a * κ ^ d) * (r / κ) ^ d + (b * κ ^ (d - 1)) * (r / κ) ^ (d - 1) * L ∧
      (b ≠ 0 → b * κ ^ (d - 1) ≠ 0) := by
  have hp (n : ℕ) : κ ^ n * (r / κ) ^ n = r ^ n := by
    rw [← mul_pow]
    congr 1
    field_simp [hκ]
  refine ⟨div_ne_zero hr hκ, ?_, ?_, ?_, fun hb => mul_ne_zero hb (pow_ne_zero _ hκ)⟩
  · rw [hC]
    field_simp [hr, hκ]
  · intro i
    rw [mul_assoc, hp]
  · calc
      _ = a * (κ ^ d * (r / κ) ^ d) + b * (κ ^ (d - 1) * (r / κ) ^ (d - 1)) * L := by rw [hp, hp]
      _ = _ := by ring

variable {J : Type*} [Field J] [Algebra J F]

/-- All rescaled cone coefficients remain algebraic over the same
actual parameter field. -/
theorem cone_root_rescaling_preserves_algebraic_coefficients
    (V : Fin 3 → F) (a b κ : F) (d : ℕ)
    (hV : ∀ i, IsAlgebraic J (V i)) (ha : IsAlgebraic J a)
    (hb : IsAlgebraic J b) (hκ : IsAlgebraic J κ) :
    (∀ i, IsAlgebraic J (V i * κ ^ d)) ∧ IsAlgebraic J (a * κ ^ d) ∧
      IsAlgebraic J (b * κ ^ (d - 1)) := by
  have hκmem := mem_algebraicClosure_iff.mpr hκ
  have hpow (n : ℕ) : κ ^ n ∈ algebraicClosure J F := by
    induction n with
    | zero => simpa only [pow_zero] using (algebraicClosure J F).one_mem
    | succ n hn => rw [pow_succ]; exact (algebraicClosure J F).mul_mem hn hκmem
  refine ⟨fun i => ?_, ?_, ?_⟩
  · exact mem_algebraicClosure_iff.mp ((algebraicClosure J F).mul_mem
      (mem_algebraicClosure_iff.mpr (hV i)) (hpow d))
  · exact mem_algebraicClosure_iff.mp ((algebraicClosure J F).mul_mem
      (mem_algebraicClosure_iff.mpr ha) (hpow d))
  · exact mem_algebraicClosure_iff.mp ((algebraicClosure J F).mul_mem
      (mem_algebraicClosure_iff.mpr hb) (hpow (d - 1)))

end DimensionFourDependence
