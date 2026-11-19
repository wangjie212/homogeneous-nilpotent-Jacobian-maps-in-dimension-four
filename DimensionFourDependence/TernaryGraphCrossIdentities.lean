import DimensionFourDependence.Nilpotent

/-! # The trace and principal-minor identities for two independent ternary rows -/

namespace DimensionFourDependence

open Matrix

variable {R : Type*} [CommRing R]

def ternaryCrossProduct (u v : Fin 3 → R) : Fin 3 → R :=
  ![u 1 * v 2 - u 2 * v 1, u 2 * v 0 - u 0 * v 2, u 0 * v 1 - u 1 * v 0]

def ternaryGraphMatrix (u v : Fin 3 → R) (p q : R) : Matrix (Fin 3) (Fin 3) R :=
  fun i => ![u, v, p • u + q • v] i

theorem ternaryCrossProduct_dot_left (u v : Fin 3 → R) :
    ternaryCrossProduct u v ⬝ᵥ u = 0 := by
  simp only [ternaryCrossProduct, dotProduct, Fin.sum_univ_three]
  simp
  ring

theorem ternaryCrossProduct_dot_right (u v : Fin 3 → R) :
    ternaryCrossProduct u v ⬝ᵥ v = 0 := by
  simp only [ternaryCrossProduct, dotProduct, Fin.sum_univ_three]
  simp
  ring

/-- The principal-minor expression in (3.3) of the cited ternary
classification is computed in the actual output graph matrix. -/
theorem ternaryGraphMatrix_trace_square_difference (u v : Fin 3 → R) (p q : R) :
    (trace (ternaryGraphMatrix u v p q)) ^ 2 -
        trace (ternaryGraphMatrix u v p q ^ 2) =
      2 * (ternaryCrossProduct u v 2 - p * ternaryCrossProduct u v 0 -
        q * ternaryCrossProduct u v 1) := by
  simp [ternaryGraphMatrix, ternaryCrossProduct, Matrix.trace, Matrix.mul_apply,
    Matrix.diag, pow_two, Fin.sum_univ_three, Pi.smul_apply, smul_eq_mul]
  ring

variable {F : Type*} [Field F] [CharZero F]

theorem nilpotent_ternaryGraphMatrix_cross_relation (u v : Fin 3 → F) (p q : F)
    (h : IsNilpotent (ternaryGraphMatrix u v p q)) :
    ternaryCrossProduct u v 2 - p * ternaryCrossProduct u v 0 - q * ternaryCrossProduct u v 1 = 0 := by
  have htr := (Matrix.isNilpotent_trace_of_isNilpotent h).eq_zero
  have htr₂ := (Matrix.isNilpotent_trace_of_isNilpotent
    (h.pow_of_pos (by decide : (2 : ℕ) ≠ 0))).eq_zero
  have he := ternaryGraphMatrix_trace_square_difference u v p q
  rw [htr, htr₂, zero_pow (by decide : (2 : ℕ) ≠ 0), sub_self] at he
  exact (mul_eq_zero.mp he.symm).resolve_left two_ne_zero

variable {R : Type*} [CommRing R]

theorem ternaryGraphMatrix_trace_from_plane_derivatives
    (u v : Fin 3 → R) (a b p q : R)
    (hx : a * u 0 + b * v 0 = -p)
    (hy : a * u 1 + b * v 1 = -q)
    (hz : a * u 2 + b * v 2 = 1) :
    trace (ternaryGraphMatrix u v p q) =
      -a * ternaryCrossProduct u v 0 - b * ternaryCrossProduct u v 1 := by
  have hp : p = -(a * u 0 + b * v 0) := by rw [hx, neg_neg]
  have hq : q = -(a * u 1 + b * v 1) := by rw [hy, neg_neg]
  rw [hp, hq]
  simp [ternaryGraphMatrix, ternaryCrossProduct, Matrix.trace, Matrix.diag,
    Fin.sum_univ_three, Pi.smul_apply, smul_eq_mul]
  linear_combination -(u 0 + v 1) * hz

end DimensionFourDependence
