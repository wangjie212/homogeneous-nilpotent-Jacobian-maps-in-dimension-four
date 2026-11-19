import DimensionFourDependence.SplitBinaryPencilBaseChange

/-! # Invertible constant changes of pencil basis preserve coprimality -/

namespace DimensionFourDependence.Shear

open MvPolynomial

variable {K : Type*} [Field K]
local notation "R₂" => MvPolynomial (Fin 2) K

/-- If a common divisor divides the two new pencil generators, multiplying
their combinations by the adjugate gives the two original generators,
each scaled by an invertible constant. -/
theorem binary_pencil_basis_preserves_isRelPrime
    (a b : R₂) (hc : IsRelPrime a b) (m n p q : K) (hd : m * q - n * p ≠ 0) :
    IsRelPrime (C m * a + C n * b) (C p * a + C q * b) := by
  let M : R₂ := C m * a + C n * b
  let N : R₂ := C p * a + C q * b
  let d := m * q - n * p
  intro k hM hN
  change k ∣ M at hM
  change k ∣ N at hN
  have hA : C q * M - C n * N = C d * a := by
    simp only [M, N, d, map_sub, map_mul]
    ring
  have hB : C m * N - C p * M = C d * b := by
    simp only [M, N, d, map_sub, map_mul]
    ring
  have hdA : k ∣ C d * a := hA ▸
    dvd_sub (dvd_mul_of_dvd_right hM _) (dvd_mul_of_dvd_right hN _)
  have hdB : k ∣ C d * b := hB ▸
    dvd_sub (dvd_mul_of_dvd_right hN _) (dvd_mul_of_dvd_right hM _)
  have hu : C d⁻¹ * C d = (1 : R₂) := by
    rw [← map_mul, inv_mul_cancel₀ hd, map_one]
  have hA' : k ∣ a := by
    simpa only [← mul_assoc, hu, one_mul] using dvd_mul_of_dvd_right hdA (C d⁻¹)
  have hB' : k ∣ b := by
    simpa only [← mul_assoc, hu, one_mul] using dvd_mul_of_dvd_right hdB (C d⁻¹)
  exact hc hA' hB'

/-- A nonzero pencil row completes to an invertible two-by-two basis
over the original field. -/
theorem binary_pencil_nonzero_row_completes_basis
    (m n : K) (hne : m ≠ 0 ∨ n ≠ 0) : ∃ p q : K, m * q - n * p ≠ 0 := by
  rcases hne with hm | hn
  · exact ⟨0, 1, by simpa using hm⟩
  · exact ⟨1, 0, by simpa using hn⟩

end DimensionFourDependence.Shear
