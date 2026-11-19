import DimensionFourDependence.ConeParameterJacobianSlope

/-! # The complete cone root expression gives the slope identity (4.9)

The root power and full last-coordinate formula determine the fixed-
parameter directional ratio. Substitution in the nilpotent slope
elimination cancels the root parameter derivative and gives exactly
the constant and linear-normal terms in (4.9).
-/

namespace DimensionFourDependence

open Matrix

set_option maxHeartbeats 4000000

variable {K F : Type*} [Field K] [Field F] [CharZero F] [Algebra K F]

omit [CharZero F] in
/-- The logarithmic derivative of a nonzero positive integral power,
written with the original root rather than its predecessor power. -/
theorem derivation_positive_power_logarithmic
    (D : Derivation K F F) (r : F) (hr : r ≠ 0) {d : ℕ} (hd : 0 < d) :
    D (r ^ d) = (d : F) * r ^ d * D r / r := by
  have hp : r ^ (d - 1) * r = r ^ d := by rw [← pow_succ]; congr 1; omega
  rw [D.leibniz_pow]
  simp only [nsmul_eq_mul, smul_eq_mul]
  rw [← hp]
  field_simp [hr]

/-- The complete cone formula determines h_V as a scalar multiple of
f_V when the coefficient and normal form are constant in that direction. -/
theorem cone_root_fixed_direction_derivative_identity
    (D : Derivation K F F) {d : ℕ} (hd : 0 < d)
    (r f h a b L : F) (hr : r ≠ 0) (hf : f = r ^ d)
    (hh : h = a * f + b * r ^ (d - 1) * L)
    (ha : D a = 0) (hb : D b = 0) (hL : D L = 0) :
    D h = (a + ((d : F) - 1) * b * L / ((d : F) * r)) * D f := by
  have hdF : (d : F) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hd)
  have hp : r ^ (d - 1) = f / r := by
    apply (eq_div_iff hr).mpr
    rw [hf, ← pow_succ]
    congr 1
    omega
  have hshape : h = a * f + b * (f / r) * L := by rw [← hp]; exact hh
  have hDf : D f = (d : F) * f * D r / r := by
    rw [hf]
    exact derivation_positive_power_logarithmic D r hr hd
  simp only [hshape, map_add, D.leibniz, D.leibniz_div, ha, hb, hL,
    smul_eq_mul, mul_zero, zero_mul, zero_add, add_zero]
  rw [hDf]
  field_simp [hr, hdF]

/-- The root parameter derivative cancels from the eliminated slope,
giving the exact two fractions in the paper's equation (4.9). -/
theorem cone_root_parameter_slope_identity
    (T : Derivation K F F) {d : ℕ} (hd : 0 < d)
    (r f h a b L α β : F) (hr : r ≠ 0) (hβ : β ≠ 0) (hf : f = r ^ d)
    (hh : h = a * f + b * r ^ (d - 1) * L) :
    (T h - (T f + α * f) * (a + ((d : F) - 1) * b * L / ((d : F) * r))) / (β * f) =
      (T a - α * a) / β +
        ((T b - α * ((d : F) - 1) * b / (d : F)) * L + b * T L) / (β * r) := by
  have hdF : (d : F) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hd)
  have hf0 : f ≠ 0 := by rw [hf]; exact pow_ne_zero d hr
  have hp : r ^ (d - 1) = f / r := by
    apply (eq_div_iff hr).mpr
    rw [hf, ← pow_succ]
    congr 1
    omega
  have hshape : h = a * f + b * (f / r) * L := by rw [← hp]; exact hh
  have hTf : T f = (d : F) * f * T r / r := by
    rw [hf]
    exact derivation_positive_power_logarithmic T r hr hd
  rw [hshape]
  simp only [map_add, T.leibniz, T.leibniz_div, smul_eq_mul]
  rw [hTf]
  field_simp [hr, hdF, hf0, hβ]
  ring

/-- The actual nilpotent parameter-update matrix and complete root
formula derive (4.9), including the fixed-direction quotient. -/
theorem nilpotent_cone_root_constructs_parameter_slope_identity
    (T D : Derivation K F F) {d : ℕ} (hd : 0 < d)
    (V A fx hx Zx : Fin 3 → F) (r f h a b L α β Zt : F)
    (hr : r ≠ 0) (hβ : β ≠ 0) (hZt : Zt ≠ 0) (hf : f = r ^ d)
    (hh : h = a * f + b * r ^ (d - 1) * L)
    (ha : D a = 0) (hb : D b = 0) (hL : D L = 0)
    (hDf : D f = fx ⬝ᵥ V) (hDh : D h = hx ⬝ᵥ V)
    (hfV : fx ⬝ᵥ V ≠ 0) (hfA : fx ⬝ᵥ A = 0) (hhA : hx ⬝ᵥ A = 0)
    (hN : IsNilpotent (coneFixedParameterJacobian V fx hx +
      Matrix.vecMulVec (coneParameterUpdateColumn V A (T f + α * f) β f (T h))
        (coneGraphParameterDifferential Zx Zt))) :
    Zx ⬝ᵥ A = (T a - α * a) / β +
      ((T b - α * ((d : F) - 1) * b / (d : F)) * L + b * T L) / (β * r) := by
  have hf0 : f ≠ 0 := by rw [hf]; exact pow_ne_zero d hr
  have hslope := nilpotent_cone_parameter_update_eliminates_graph_slope
    V A fx hx Zx (T f + α * f) β f (T h) Zt hZt hfA hhA hN hfV hβ hf0
  have hratio : (hx ⬝ᵥ V) / (fx ⬝ᵥ V) = a + ((d : F) - 1) * b * L / ((d : F) * r) := by
    apply (div_eq_iff hfV).mpr
    have he := cone_root_fixed_direction_derivative_identity D hd r f h a b L hr hf hh ha hb hL
    rwa [hDf, hDh] at he
  rw [hslope, mul_div_assoc, hratio]
  exact cone_root_parameter_slope_identity T hd r f h a b L α β hr hβ hf hh

end DimensionFourDependence
