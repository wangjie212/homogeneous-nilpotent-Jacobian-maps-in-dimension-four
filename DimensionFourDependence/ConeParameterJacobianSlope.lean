import DimensionFourDependence.RankOneUpdateTrace

/-! # Nilpotence derives the cone parameter slope equations of (4.8)

The fixed-parameter matrix has upper block V f_x, bottom row h_x,
and zero fourth column. Its square trace is its squared trace. The
parameter column and actual graph differential turn the two nilpotent
rank-one-update identities into the scalar equations used to eliminate
Z_t and obtain the slope in (4.9).
-/

namespace DimensionFourDependence

open Matrix

set_option maxHeartbeats 4000000

variable {R : Type*} [CommRing R]

/-- The fixed-parameter part of the actual cone Jacobian (4.8). -/
def coneFixedParameterJacobian (V fx hx : Fin 3 → R) : Matrix (Fin 4) (Fin 4) R :=
  !![V 0 * fx 0, V 0 * fx 1, V 0 * fx 2, 0;
     V 1 * fx 0, V 1 * fx 1, V 1 * fx 2, 0;
     V 2 * fx 0, V 2 * fx 1, V 2 * fx 2, 0;
     hx 0, hx 1, hx 2, 0]

/-- The parameter column after writing V' = alpha V + beta A. -/
def coneParameterUpdateColumn (V A : Fin 3 → R) (q β f ht : R) : Fin 4 → R :=
  Fin.snoc (fun i => q * V i + β * f * A i) ht

/-- The exact trace of the fixed-parameter cone block. -/
theorem cone_fixed_parameter_jacobian_trace (V fx hx : Fin 3 → R) :
    Matrix.trace (coneFixedParameterJacobian V fx hx) = fx ⬝ᵥ V := by
  simp [coneFixedParameterJacobian, Matrix.trace, Matrix.diag, dotProduct, Fin.sum_univ_succ]
  ring

/-- The fixed-parameter cone block has zero second characteristic
coefficient, expressed without division by two. -/
theorem cone_fixed_parameter_jacobian_square_trace (V fx hx : Fin 3 → R) :
    Matrix.trace (coneFixedParameterJacobian V fx hx * coneFixedParameterJacobian V fx hx) =
      Matrix.trace (coneFixedParameterJacobian V fx hx) ^ 2 := by
  rw [cone_fixed_parameter_jacobian_trace]
  simp [coneFixedParameterJacobian, Matrix.trace, Matrix.diag, Matrix.mul_apply, dotProduct, Fin.sum_univ_succ]
  ring

/-- Constancy along the projected fiber direction gives the full
matrix action on the parameter column, including its fourth entry. -/
theorem cone_fixed_parameter_jacobian_mul_parameter_column
    (V A fx hx : Fin 3 → R) (q β f ht : R) (hfA : fx ⬝ᵥ A = 0) (hhA : hx ⬝ᵥ A = 0) :
    coneFixedParameterJacobian V fx hx *ᵥ coneParameterUpdateColumn V A q β f ht =
      Fin.snoc (fun i => q * (fx ⬝ᵥ V) * V i) (q * (hx ⬝ᵥ V)) := by
  simp [dotProduct, Fin.sum_univ_succ] at hfA hhA
  funext i
  fin_cases i <;>
    simp [coneFixedParameterJacobian, coneParameterUpdateColumn, Fin.snoc, Fin.castPred, Fin.castLT,
      mulVec, dotProduct, Fin.sum_univ_succ]
  · linear_combination V 0 * β * f * hfA
  · linear_combination V 1 * β * f * hfA
  · linear_combination V 2 * β * f * hfA
  · linear_combination β * f * hhA

variable {F : Type*} [Field F]

/-- The actual parameter differential in the graph w = Z(t,x). -/
def coneGraphParameterDifferential (Zx : Fin 3 → F) (Zt : F) : Fin 4 → F :=
  Fin.snoc (fun i => -Zx i / Zt) (1 / Zt)

variable [CharZero F]

/-- The actual nilpotent update derives both scalar equations of
(4.8), without supplied trace identities or scalar eliminations. -/
theorem nilpotent_cone_parameter_update_slope_equations
    (V A fx hx Zx : Fin 3 → F) (q β f ht Zt : F) (hZt : Zt ≠ 0)
    (hfA : fx ⬝ᵥ A = 0) (hhA : hx ⬝ᵥ A = 0)
    (hN : IsNilpotent (coneFixedParameterJacobian V fx hx +
      Matrix.vecMulVec (coneParameterUpdateColumn V A q β f ht) (coneGraphParameterDifferential Zx Zt))) :
    (fx ⬝ᵥ V) * Zt = q * (Zx ⬝ᵥ V) + β * f * (Zx ⬝ᵥ A) - ht ∧
      q * (hx ⬝ᵥ V - (fx ⬝ᵥ V) * (Zx ⬝ᵥ V)) = -(fx ⬝ᵥ V) ^ 2 * Zt := by
  have hp := nilpotent_rank_one_update_pairings (coneFixedParameterJacobian V fx hx)
    (coneParameterUpdateColumn V A q β f ht) (coneGraphParameterDifferential Zx Zt)
    (cone_fixed_parameter_jacobian_square_trace V fx hx) hN
  have hfirst : coneGraphParameterDifferential Zx Zt ⬝ᵥ coneParameterUpdateColumn V A q β f ht =
      (ht - q * (Zx ⬝ᵥ V) - β * f * (Zx ⬝ᵥ A)) / Zt := by
    simp [coneGraphParameterDifferential, coneParameterUpdateColumn, Fin.snoc, Fin.castPred, Fin.castLT,
      dotProduct, Fin.sum_univ_succ]
    field_simp [hZt]
    ring
  have hsecond : coneGraphParameterDifferential Zx Zt ⬝ᵥ
      (coneFixedParameterJacobian V fx hx *ᵥ coneParameterUpdateColumn V A q β f ht) =
      q * (hx ⬝ᵥ V - (fx ⬝ᵥ V) * (Zx ⬝ᵥ V)) / Zt := by
    rw [cone_fixed_parameter_jacobian_mul_parameter_column V A fx hx q β f ht hfA hhA]
    simp [coneGraphParameterDifferential, Fin.snoc, Fin.castPred, Fin.castLT, dotProduct, Fin.sum_univ_succ]
    field_simp [hZt]
    ring
  rw [cone_fixed_parameter_jacobian_trace, hfirst, hsecond] at hp
  refine ⟨?_, (div_eq_iff hZt).mp hp.2⟩
  have he := (div_eq_iff hZt).mp hp.1
  linear_combination he

/-- Eliminating the parameter derivative in the two actual nilpotent
equations gives the cone slope before substituting the root formula. -/
theorem nilpotent_cone_parameter_update_eliminates_graph_slope
    (V A fx hx Zx : Fin 3 → F) (q β f ht Zt : F) (hZt : Zt ≠ 0)
    (hfA : fx ⬝ᵥ A = 0) (hhA : hx ⬝ᵥ A = 0)
    (hN : IsNilpotent (coneFixedParameterJacobian V fx hx +
      Matrix.vecMulVec (coneParameterUpdateColumn V A q β f ht) (coneGraphParameterDifferential Zx Zt)))
    (hfV : fx ⬝ᵥ V ≠ 0) (hβ : β ≠ 0) (hf : f ≠ 0) :
    Zx ⬝ᵥ A = (ht - q * (hx ⬝ᵥ V) / (fx ⬝ᵥ V)) / (β * f) := by
  obtain ⟨hfirst, hsecond⟩ := nilpotent_cone_parameter_update_slope_equations
    V A fx hx Zx q β f ht Zt hZt hfA hhA hN
  apply (eq_div_iff (mul_ne_zero hβ hf)).mpr
  field_simp [hfV]
  linear_combination -(fx ⬝ᵥ V) * hfirst + hsecond

end DimensionFourDependence
