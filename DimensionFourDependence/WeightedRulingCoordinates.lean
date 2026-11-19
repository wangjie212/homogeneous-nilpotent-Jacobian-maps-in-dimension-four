import DimensionFourDependence.RulingDirectionAcceleration
import DimensionFourDependence.WeightedAffineRootFactorization

/-! # Actual directional and Euler coordinates for the weighted ruling function

Parameter-algebraic directions are Euler constants as well as directional
constants. Their directional commutator with the output Euler field is
the direction itself. A nonzero weighted function with zero acceleration
forces a nonzero transverse linear coordinate.
-/

namespace DimensionFourDependence

open Matrix

variable {K F : Type*} [Field K] [Field F] [Algebra K F] {n : ℕ}

/-- An Euler-constant direction has commutator equal to itself with
the actual coordinate Euler derivation. -/
theorem coordinate_direction_euler_commutator
    (δ : Fin n → Derivation K F F) (y v : Fin n → F)
    (hcoord : ∀ i j, δ i (y j) = if j = i then 1 else 0)
    (hcomm : ∀ i j x, δ i (δ j x) = δ j (δ i x))
    (hv : ∀ i, coordinateEuler y δ (v i) = 0) (x : F) :
    coordinateEuler v δ (coordinateEuler y δ x) =
      coordinateEuler y δ (coordinateEuler v δ x) + coordinateEuler v δ x := by
  have he : coordinateEuler y δ (coordinateEuler v δ x) =
      ∑ i, v i * coordinateEuler y δ (δ i x) := by
    rw [coordinateEuler_apply v δ x, map_sum]
    simp only [Derivation.leibniz, hv, smul_eq_mul, mul_zero, add_zero]
  rw [he]
  simp only [coordinateEuler_apply v δ, coordinatePartial_euler y δ hcoord hcomm,
    mul_add, Finset.sum_add_distrib]

variable [CharZero K]

/-- The output weight 1+1/d of a positive-degree homogeneous map is
nonzero in every characteristic-zero coefficient extension. -/
theorem one_add_inverse_positive_natCast_ne_zero [CharZero F] {d : ℕ} (hd : 0 < d) :
    (1 + (d : F)⁻¹) ≠ 0 := by
  have hd0 : (d : F) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hd)
  intro hz
  have he := congrArg (fun x : F => x * (d : F)) hz
  simp only [add_mul, one_mul, inv_mul_cancel₀ hd0, zero_mul] at he
  have hs : ((d + 1 : ℕ) : F) = 0 := by
    simpa only [Nat.cast_add, Nat.cast_one] using he
  exact (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero d)) hs

/-- A nonzero function of weight 1+1/d and zero directional
acceleration forces an actual transverse coordinate. The longitudinal
coordinate is normalized using a nonzero actual direction entry. -/
theorem weighted_zero_acceleration_exists_transverse_coordinate
    (δ : Fin n → Derivation K F F) (y v : Fin n → F)
    (hcoord : ∀ i j, δ i (y j) = if j = i then 1 else 0)
    (hv : v ≠ 0) (hvD : ∀ i, coordinateEuler v δ (v i) = 0)
    {d : ℕ} (hd : 0 < d) (f : F) (hf : f ≠ 0)
    (hsecond : coordinateEuler v δ (coordinateEuler v δ f) = 0)
    (hweight : coordinateEuler y δ f = (1 + (d : F)⁻¹) * f) :
    ∃ a b : Fin n, v a ≠ 0 ∧ y b - v b * (y a / v a) ≠ 0 := by
  let : CharZero F := charZero_of_injective_algebraMap (algebraMap K F).injective
  obtain ⟨a, ha⟩ : ∃ a, v a ≠ 0 := by
    simpa only [ne_eq, funext_iff, Pi.zero_apply, not_forall] using hv
  let D := coordinateEuler v δ
  let E := coordinateEuler y δ
  let r := y a / v a
  have hr : D r = 1 := by
    rw [show r = y a / v a from rfl, D.leibniz_div]
    rw [coordinate_direction_coordinate δ y v hcoord a, hvD a]
    simp only [smul_eq_mul, mul_zero, sub_zero]
    field_simp
  by_contra hn
  have hline (b : Fin n) : y b = v b * r := by
    by_contra hh
    exact hn ⟨a, b, ha, sub_ne_zero.mpr hh⟩
  have hED (x : F) : E x = r * D x := by
    simp only [E, D, coordinateEuler_apply, hline, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hwD : D (1 + (d : F)⁻¹) = 0 := by
    rw [map_add, D.map_one_eq_zero, derivation_inv_natCast_zero, zero_add]
  have hDf : D f = 0 := by
    have he := congrArg D hweight
    change D (E f) = D ((1 + (d : F)⁻¹) * f) at he
    rw [hED, D.leibniz, hr, hsecond, D.leibniz, hwD] at he
    simp only [smul_eq_mul, mul_zero, mul_one, zero_add, add_zero] at he
    have hz : (d : F)⁻¹ * D f = 0 := by linear_combination -he
    exact (mul_eq_zero.mp hz).resolve_left (inv_ne_zero (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hd)))
  have he := hweight
  change E f = (1 + (d : F)⁻¹) * f at he
  rw [hED, hDf, mul_zero] at he
  exact (mul_ne_zero (one_add_inverse_positive_natCast_ne_zero (F := F) hd) hf) he.symm

end DimensionFourDependence
