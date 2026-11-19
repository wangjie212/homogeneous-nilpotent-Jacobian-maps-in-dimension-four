import DimensionFourDependence.QuinticAffineShearFrames
import DimensionFourDependence.QuinticPolynomialCoordinates

/-! # Actual polynomial tame shears on the two active planes -/

namespace DimensionFourDependence.Quintic

open MvPolynomial

set_option maxHeartbeats 1000000

variable {K : Type*} [Field K] [CharZero K]
local notation "R₃" => MvPolynomial (Fin 3) K
local notation "R₄" => MvPolynomial (Fin 4) K
local notation "Aut₄" => R₄ ≃ₐ[K] R₄

/-- The shear in (6.23) and (6.37) with every allowed parameter. -/
theorem tame_xy_invariant_shear (f : R₃) :
    ∃ E : Aut₄, E ∈ Tame.subgroup K 4 ∧
      let u := coordinateU (X 0 : R₄) (X 1) (X 2) (X 3)
      let k := aeval ![u, X 3, X 2] f
      ∀ i, E (X i) = ![X 0 - X 2 * k, X 1 + X 3 * k, X 2, X 3] i := by
  obtain ⟨E, hE, h⟩ := determinant_shear_in_tame_coordinates xyShearFrame xyShearFrame_tame (-f)
  dsimp only at h
  have hx : xyShearFrame (X 0 : R₄) = X 0 := xyShearFrame_X 0
  have hy : xyShearFrame (X 1 : R₄) = -X 1 := xyShearFrame_X 1
  have hz : xyShearFrame (X 3 : R₄) = X 2 := xyShearFrame_X 3
  have ht : xyShearFrame (X 2 : R₄) = X 3 := xyShearFrame_X 2
  let u : R₄ := coordinateU (X 0) (X 1) (X 2) (X 3)
  let k : R₄ := aeval ![u, X 3, X 2] f
  have hu : (X 3 * X 0 - X 2 * -X 1 : R₄) = u := by
    simp only [coordinateU, u, mul_neg, sub_neg_eq_add]
  simp only [hx, hy, hz, ht, hu, map_neg] at h
  refine ⟨E, hE, ?_⟩
  change ∀ i : Fin 4, E (X i) = ![X 0 - X 2 * k, X 1 + X 3 * k, X 2, X 3] i
  intro i
  fin_cases i
  · change E (X 0) = X 0 - X 2 * k
    simpa only [sub_eq_add_neg, mul_neg] using h.1
  · change E (X 1) = X 1 + X 3 * k
    have he : -E (X 1) = -(X 1 + X 3 * k) := by
      simpa only [mul_neg, neg_add_rev, add_comm] using h.2.1
    exact neg_injective he
  · exact h.2.2.2
  · exact h.2.2.1

/-- The shear on x and z, with coefficient coordinate y+c. This is
used with both signs of the constant offset in Section 6.5. -/
theorem tame_xz_invariant_shear (c : K) (f : R₃) :
    ∃ E : Aut₄, E ∈ Tame.subgroup K 4 ∧
      let β : R₄ := X 1 + C c
      let q := aeval ![X 3 * X 0 + β * X 2, X 3, β] f
      ∀ i, E (X i) = ![X 0 + β * q, X 1, X 2 - X 3 * q, X 3] i := by
  obtain ⟨E, hE, h⟩ := determinant_shear_in_tame_coordinates (xzShearFrame c) (xzShearFrame_tame c) f
  dsimp only at h
  let β : R₄ := X 1 + C c
  let q : R₄ := aeval ![X 3 * X 0 + β * X 2, X 3, β] f
  have hx : xzShearFrame c (X 0) = X 0 := xzShearFrame_X c 0
  have hz : xzShearFrame c (X 1) = -X 2 := xzShearFrame_X c 1
  have ht : xzShearFrame c (X 2) = X 3 := xzShearFrame_X c 2
  have hy : xzShearFrame c (X 3) = β := xzShearFrame_X c 3
  simp only [hx, hy, hz, ht, mul_neg, sub_neg_eq_add, map_neg] at h
  have hy' : E (X 1) = X 1 := by
    have he : E (X 1 + C c) = X 1 + C c := h.2.2.2
    have hC : E (C c) = C c := E.commutes c
    rw [map_add, hC] at he
    exact add_right_cancel he
  refine ⟨E, hE, ?_⟩
  change ∀ i : Fin 4, E (X i) = ![X 0 + β * q, X 1, X 2 - X 3 * q, X 3] i
  intro i
  fin_cases i
  · exact h.1
  · exact hy'
  · change E (X 2) = X 2 - X 3 * q
    have he : -E (X 2) = -(X 2 - X 3 * q) := by
      calc
        _ = -X 2 + X 3 * q := h.2.1
        _ = _ := by ring
    exact neg_injective he
  · exact h.2.2.1

end DimensionFourDependence.Quintic
