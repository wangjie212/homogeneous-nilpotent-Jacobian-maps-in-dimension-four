import DimensionFourDependence.NormalCodimensionOneRegularity

/-! # A regular numerator quotient forces the original ideal-power multiplicity -/

namespace DimensionFourDependence

variable {R F : Type*} [CommRing R] [IsDomain R] [Field F]
  [Algebra R F] [IsFractionRing R F]

/-- Regularity of the exact quotient by a power makes the original
numerator divisible by that denominator power in the actual regular ring. -/
theorem regular_quotient_constructs_numerator_multiple
    (n l : R) (hl : l ≠ 0) (d : ℕ)
    (hreg : IsLocalization.IsInteger R (algebraMap R F n / (algebraMap R F l) ^ d)) :
    ∃ u : R, n = u * l ^ d := by
  obtain ⟨u, hu⟩ := hreg
  have hlF : algebraMap R F l ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective R F)).mpr hl
  have he := (eq_div_iff (pow_ne_zero d hlF)).mp hu
  refine ⟨u, (IsFractionRing.injective R F) ?_⟩
  simpa only [map_mul, map_pow] using he.symm

/-- A denominator in an ideal and a regular exact quotient force
the numerator into the corresponding ideal power. -/
theorem regular_quotient_numerator_mem_ideal_power
    (J : Ideal R) (n l : R) (hl : l ≠ 0) (hlJ : l ∈ J) (d : ℕ)
    (hreg : IsLocalization.IsInteger R (algebraMap R F n / (algebraMap R F l) ^ d)) :
    n ∈ J ^ d := by
  obtain ⟨u, he⟩ := regular_quotient_constructs_numerator_multiple n l hl d hreg
  rw [he]
  apply Ideal.mul_mem_left
  exact Ideal.pow_mem_pow hlJ d

end DimensionFourDependence
