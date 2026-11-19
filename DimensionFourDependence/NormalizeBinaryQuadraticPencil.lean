import DimensionFourDependence.BinaryPencilBasisCoprimality
import DimensionFourDependence.NormalizeBinaryPencilSecondForm

/-! # Lemma 6.8: the exact original-field binary pencil normal form -/

namespace DimensionFourDependence.Shear

open MvPolynomial Matrix

variable {K : Type*} [Field K] [CharZero K]
local notation "R₂" => MvPolynomial (Fin 2) K
local notation "M₂" => Matrix (Fin 2) (Fin 2) K

/-- The actual constant base frame and an invertible pencil basis realize
the two simultaneous identities (6.44) over the given field. -/
theorem lemma_6_8 (a b : R₂) (hc : IsRelPrime a b)
    (ha : a.IsHomogeneous 2) (hb : b.IsHomogeneous 2) :
    ∃ T S : M₂, T * S = 1 ∧ S * T = 1 ∧
      ∃ m n p q η : K, m * q - n * p ≠ 0 ∧ η ≠ 0 ∧
        C m * linearPolynomialPullback T a + C n * linearPolynomialPullback T b = X 0 * X 1 ∧
        C p * linearPolynomialPullback T a + C q * linearPolynomialPullback T b =
          X 0 ^ 2 + C η * X 1 ^ 2 := by
  obtain ⟨r, s, k, μ, ν, hrs, hk, hrow, hsplit⟩ :=
    coprime_binary_quadratic_pencil_constructs_split_member a b hc ha hb
  obtain ⟨T, S, hTS, hST, hr, hs⟩ := split_binary_quadratic_factors_construct_base_frame r s hrs
  let φ : R₂ →ₐ[K] R₂ := aeval (linearPolynomialMap T)
  let α := φ a
  let β := φ b
  have hφ (c : K) : φ (C c) = C c := φ.commutes c
  have hr' : φ (X 0 - C r * X 1) = X 0 := hr
  have hs' : φ (X 0 - C s * X 1) = X 1 := hs
  have htrans : C μ * α + C ν * β = C k * X 0 * X 1 := by
    have he := congrArg φ hsplit
    simpa only [map_add, map_mul, hφ, hr', hs'] using he
  let m := k⁻¹ * μ
  let n := k⁻¹ * ν
  have hk' : k⁻¹ ≠ 0 := inv_ne_zero hk
  have hfirst : C m * α + C n * β = X 0 * X 1 := by
    have hu : C k⁻¹ * C k = (1 : R₂) := by rw [← map_mul, inv_mul_cancel₀ hk, map_one]
    calc
      _ = C k⁻¹ * (C μ * α + C ν * β) := by simp only [m, n, map_mul]; ring
      _ = _ := by rw [htrans, ← mul_assoc, ← mul_assoc, hu, one_mul]
  have hm : m ≠ 0 ∨ n ≠ 0 :=
    hrow.imp (mul_ne_zero hk') (mul_ne_zero hk')
  obtain ⟨p, q, hpq⟩ := binary_pencil_nonzero_row_completes_basis m n hm
  let F : R₂ := C p * α + C q * β
  have hc' : IsRelPrime α β := binary_base_frame_preserves_isRelPrime T S hTS hST a b hc
  have hF : IsRelPrime (X 0 * X 1) F := by
    rw [← hfirst]
    exact binary_pencil_basis_preserves_isRelPrime α β hc' m n p q hpq
  have hFh : F.IsHomogeneous 2 :=
    ((linearPolynomialPullback_homogeneous T a ha).C_mul p).add
      ((linearPolynomialPullback_homogeneous T b hb).C_mul q)
  obtain ⟨A, B, η, hA, hη, he⟩ := normalize_binary_pencil_second_form F hFh hF
  let v := -A⁻¹ * B
  let w := A⁻¹
  let p' := v * m + w * p
  let q' := v * n + w * q
  refine ⟨T, S, hTS, hST, m, n, p', q', η, ?_, hη, hfirst, ?_⟩
  · have hdet : m * q' - n * p' = w * (m * q - n * p) := by
      dsimp only [p', q']
      ring
    exact hdet ▸ mul_ne_zero (inv_ne_zero hA) hpq
  · change C p' * α + C q' * β = _
    calc
      _ = C v * (C m * α + C n * β) + C w * F := by
        simp only [p', q', F, map_add, map_mul]
        ring
      _ = _ := by rw [hfirst]; exact he

end DimensionFourDependence.Shear
