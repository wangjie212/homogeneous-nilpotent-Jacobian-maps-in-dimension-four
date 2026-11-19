import DimensionFourDependence.HomogeneousBinaryQuadraticCoefficients
import DimensionFourDependence.CoprimeBinaryPencilLeadingMinors

/-! # Normalizing the second pencil member after the first is the product -/

namespace DimensionFourDependence.Shear

open MvPolynomial

variable {K : Type*} [Field K]
local notation "R₂" => MvPolynomial (Fin 2) K

/-- Coprimality with the product of the coordinate variables forces both
square coefficients to be nonzero. Subtracting the mixed term and
scaling yields the second normal form in (6.44). -/
theorem normalize_binary_pencil_second_form (p : R₂)
    (hp : p.IsHomogeneous 2) (hc : IsRelPrime (X 0 * X 1) p) :
    ∃ A B η : K, A ≠ 0 ∧ η ≠ 0 ∧
      C (-A⁻¹ * B) * (X 0 * X 1) + C A⁻¹ * p = X 0 ^ 2 + C η * X 1 ^ 2 := by
  obtain ⟨A, B, D, he⟩ := homogeneous_binary_quadratic_expansion p hp
  have hunit (i : Fin 2) : ¬IsUnit (X i : R₂) :=
    positive_degree_binary_form_not_isUnit (X i) (isHomogeneous_X _ _) (by decide)
  have ha : A ≠ 0 := by
    intro hz
    apply hunit 1 (hc (dvd_mul_left _ _) ?_)
    refine ⟨C B * X 0 + C D * X 1, ?_⟩
    simp only [he, hz, map_zero, zero_mul, zero_add]
    ring
  have hd : D ≠ 0 := by
    intro hz
    apply hunit 0 (hc (dvd_mul_right _ _) ?_)
    refine ⟨C A * X 0 + C B * X 1, ?_⟩
    simp only [he, hz, map_zero, zero_mul, add_zero]
    ring
  refine ⟨A, B, A⁻¹ * D, ha, mul_ne_zero (inv_ne_zero ha) hd, ?_⟩
  let a : R₂ := C A
  let i : R₂ := C A⁻¹
  let b : R₂ := C B
  let c : R₂ := C D
  have hi : i * a = 1 := by
    change C A⁻¹ * C A = (1 : R₂)
    rw [← map_mul, inv_mul_cancel₀ ha, map_one]
  rw [he]
  simp only [map_neg, map_mul]
  change (-i * b) * (X 0 * X 1) + i * (a * X 0 ^ 2 + b * X 0 * X 1 + c * X 1 ^ 2) =
    X 0 ^ 2 + (i * c) * X 1 ^ 2
  calc
    _ = (i * a) * X 0 ^ 2 + (i * c) * X 1 ^ 2 := by ring
    _ = _ := by rw [hi, one_mul]

end DimensionFourDependence.Shear
