import DimensionFourDependence.Tame

/-! # The polynomial commutator calculation in equation (6.13) -/

namespace DimensionFourDependence.TernaryNormalForm

set_option maxHeartbeats 3000000

variable {K A : Type*} [CommRing K] [CommRing A] [Algebra K A]

/-- The entire calculation takes place in a commutative algebra.
The equations specify the actual values of all four factors. -/
theorem normal_form_commutator_identity
    (U V I J : A →ₐ[K] A) (x : Fin 4 → A) (q : A)
    (hU : ∀ i, U (x i) = ![x 0 + x 3 * x 2,
      x 1 - 2 * x 0 * x 2 - x 3 * x 2 ^ 2, x 2, x 3] i)
    (hV : ∀ i, V (x i) = ![x 0, x 1, x 2 + q, x 3] i)
    (hI : ∀ i, I (x i) = ![x 0 - x 3 * x 2,
      x 1 + 2 * x 0 * x 2 - x 3 * x 2 ^ 2, x 2, x 3] i)
    (hJ : ∀ i, J (x i) = ![x 0, x 1, x 2 - q, x 3] i)
    (hi : I q = q) (hj : J q = q) :
    ∀ i, J (I (V (U (x i)))) =
      ![x 0 + x 3 * q, x 1 - 2 * x 0 * q - x 3 * q ^ 2, x 2, x 3] i := by
  have hv₂ : V 2 = 2 := map_ofNat V 2
  have hi₂ : I 2 = 2 := map_ofNat I 2
  have hj₂ : J 2 = 2 := map_ofNat J 2
  intro i
  rw [hU]
  fin_cases i <;>
    simp [map_add, map_sub, map_mul, map_pow, hV, hI, hJ, hi, hj, hv₂, hi₂, hj₂] <;> ring

/-- The last two elementary factors cancel the quadratic term of the
commutator. The homomorphisms remain abstract throughout the calculation. -/
theorem normal_form_finishing_identity
    (W U V : A ≃ₐ[K] A) (x : Fin 4 → A) (q r : A) (e : ℕ)
    (hW : ∀ i, W (x i) = ![x 0 + x 3 * q, x 1 - 2 * x 0 * q - x 3 * q ^ 2, x 2, x 3] i)
    (hU : ∀ i, U (x i) = ![x 0, x 1, x 2 + r, x 3] i)
    (hV : ∀ i, V (x i) = ![x 0, x 1 + x 3 ^ e * x 2, x 2, x 3] i)
    (hr : W r = r) (hc : x 3 ^ e * r = x 3 * q ^ 2) :
    ∀ i, (W * U * V) (x i) =
      ![x 0 + x 3 * q, x 1 + (x 3 ^ e * x 2 - 2 * x 0 * q), x 2 + r, x 3] i := by
  intro i
  simp only [AlgEquiv.mul_apply]
  rw [hV]
  fin_cases i <;> simp [map_add, map_mul, map_pow, hU, hW, hr]
  linear_combination hc

theorem normal_form_coordinatewise_addition (x : Fin 4 → A) (a b c : A) (j : Fin 4) :
    ![x 0 + a, x 1 + b, x 2 + c, x 3] j = x j + ![a, b, c, 0] j := by
  fin_cases j <;> simp

end DimensionFourDependence.TernaryNormalForm
