import DimensionFourDependence.CoprimeBinaryPencilLeadingMinors
import DimensionFourDependence.BinaryPencilSimpleSpecialization

/-! # The pencil contains a split member over the original field -/

namespace DimensionFourDependence.Shear

open MvPolynomial

variable {K : Type*} [Field K] [CharZero K]
local notation "R₂" => MvPolynomial (Fin 2) K

private theorem binary_quadratic_linear_combination {R : Type*} [CommRing R]
    (a₂ a₁ a₀ b₂ b₁ b₀ m n x y : R) :
    m * (a₂ * x ^ 2 + a₁ * x * y + a₀ * y ^ 2) +
        n * (b₂ * x ^ 2 + b₁ * x * y + b₀ * y ^ 2) =
      (m * a₂ + n * b₂) * x ^ 2 + (m * a₁ + n * b₁) * x * y +
        (m * a₀ + n * b₀) * y ^ 2 := by ring

/-- The split member of Lemma 6.8 has a nonzero coefficient and two
distinct linear factors, all defined over the given field. -/
theorem coprime_binary_quadratic_pencil_constructs_split_member
    (a b : R₂) (hc : IsRelPrime a b) (ha : a.IsHomogeneous 2) (hb : b.IsHomogeneous 2) :
    ∃ r s k m n : K, r ≠ s ∧ k ≠ 0 ∧ (m ≠ 0 ∨ n ≠ 0) ∧
      C m * a + C n * b = C k * (X 0 - C r * X 1) * (X 0 - C s * X 1) := by
  obtain ⟨a₂, a₁, a₀, hA⟩ := homogeneous_binary_quadratic_expansion a ha
  obtain ⟨b₂, b₁, b₀, hB⟩ := homogeneous_binary_quadratic_expansion b hb
  have hm := coprime_binary_quadratic_pencil_leading_minors a b hc ha hb a₂ a₁ a₀ b₂ b₁ b₀ hA hB
  obtain ⟨r, hr⟩ := binary_pencil_simple_affine_specialization a₂ a₁ a₀ b₂ b₁ b₀ hm
  let u := a₂ * r ^ 2 + a₁ * r + a₀
  let v := b₂ * r ^ 2 + b₁ * r + b₀
  let k := v * a₂ - u * b₂
  let l := v * a₁ - u * b₁
  let w := v * a₀ - u * b₀
  have hk : k ≠ 0 := hr.1
  have hsimp : 2 * k * r + l ≠ 0 := hr.2
  have hroot : k * r ^ 2 + l * r + w = 0 := by
    change (v * a₂ - u * b₂) * r ^ 2 + (v * a₁ - u * b₁) * r + (v * a₀ - u * b₀) = 0
    calc
      _ = v * (a₂ * r ^ 2 + a₁ * r + a₀) - u * (b₂ * r ^ 2 + b₁ * r + b₀) := by ring
      _ = 0 := by
        change v * u - u * v = 0
        rw [mul_comm v u, sub_self]
  obtain ⟨s, hrs, hsplit⟩ := binary_quadratic_splits_at_simple_affine_root k l w r hk hroot hsimp
  refine ⟨r, s, k, v, -u, Ne.symm hrs, hk, ?_, ?_⟩
  · by_contra! hz
    apply hk
    simp [k, hz.1, neg_eq_zero.mp hz.2]
  · rw [hA, hB, binary_quadratic_linear_combination, ← hsplit]
    simp only [k, l, w, sub_eq_add_neg, map_add, map_mul, map_neg, neg_mul]

end DimensionFourDependence.Shear
