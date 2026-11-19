import DimensionFourDependence.BinaryQuadraticExpansion

/-! # A simple affine root splits a binary quadratic over the original field -/

namespace DimensionFourDependence.Shear

open MvPolynomial

variable {K : Type*} [Field K]
local notation "R₂" => MvPolynomial (Fin 2) K

private theorem binary_quadratic_product {R : Type*} [CommRing R] (a r s x y : R) :
    a * (x - r * y) * (x - s * y) =
      a * x ^ 2 + (-(a * r + a * s)) * x * y + (a * r * s) * y ^ 2 := by
  ring

/-- The second affine root is computed in the original field, and
the homogeneous factorization has two distinct linear factors. -/
theorem binary_quadratic_splits_at_simple_affine_root
    (a b c r : K) (ha : a ≠ 0) (hroot : a * r ^ 2 + b * r + c = 0)
    (hsimple : 2 * a * r + b ≠ 0) :
    ∃ s : K, s ≠ r ∧
      (C a * X 0 ^ 2 + C b * X 0 * X 1 + C c * X 1 ^ 2 : R₂) =
        C a * (X 0 - C r * X 1) * (X 0 - C s * X 1) := by
  let s := -b / a - r
  have hs : a * s = -b - a * r := by
    dsimp [s]
    field_simp
  have hb : -(a * r + a * s) = b := by rw [hs]; ring
  have hc : a * r * s = c := by
    calc
      a * r * s = r * (a * s) := by ring
      _ = c := by rw [hs]; linear_combination -hroot
  refine ⟨s, ?_, ?_⟩
  · intro he
    apply hsimple
    rw [he] at hs
    calc
      2 * a * r + b = a * r - (-b - a * r) := by ring
      _ = 0 := sub_eq_zero.mpr hs
  · let x : R₂ := X 0
    let y : R₂ := X 1
    change C a * x ^ 2 + C b * x * y + C c * y ^ 2 =
      C a * (x - C r * y) * (x - C s * y)
    have hb' : -(C a * C r + C a * C s) = (C b : R₂) := by
      simpa only [map_neg, map_add, map_mul] using congrArg (C : K →+* R₂) hb
    have hc' : C a * C r * C s = (C c : R₂) := by
      simpa only [map_mul] using congrArg (C : K →+* R₂) hc
    rw [binary_quadratic_product, hb', hc']

end DimensionFourDependence.Shear
