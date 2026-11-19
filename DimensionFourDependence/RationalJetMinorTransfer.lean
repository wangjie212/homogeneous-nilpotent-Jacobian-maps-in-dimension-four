import DimensionFourDependence.RationalCoverJetComparison

/-! # The actual normal-jet minor survives parameter covers and field realizations -/

namespace DimensionFourDependence

open Matrix

set_option maxHeartbeats 4000000

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

/-- The exact normalized three-column jet determinant changes by
the cube of the actual parameter speed. The second-speed derivative
cancels, including after a coefficient-field embedding. -/
theorem rational_normal_jet_minor_transfer
    (f : RatFunc K →ₐ[K] F) (T : Derivation K F F)
    (v : Fin 4 → RatFunc K) (a i j : Fin 4) (ha : v a = 1) :
    ((normalCharacteristicMatrix T (fun k => f (v k))).submatrix id ![a, i, j]).det =
      f (((rationalParameterJetMatrix v).submatrix id ![a, i, j]).det) * T (f RatFunc.X) ^ 3 := by
  rw [rationalParameterJetMatrix_det_normalized_column v a i j ha]
  simp only [normalCharacteristicMatrix, Matrix.det_fin_three, Matrix.submatrix_apply, id_eq,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, ha, map_one,
    Derivation.map_one_eq_zero, map_zero, zero_mul, mul_zero, sub_zero, zero_add]
  rw [rational_parameter_second_chain_rule f T (v i), rational_parameter_second_chain_rule f T (v j),
    rational_parameter_chain_rule f T (v i), rational_parameter_chain_rule f T (v j)]
  simp only [map_sub, map_mul]
  ring

/-- A nonzero original normalized jet minor and nonzero actual
parameter speed construct independence of all three realized normal jets. -/
theorem rational_normal_jet_independent_after_parameter_realization
    (f : RatFunc K →ₐ[K] F) (T : Derivation K F F)
    (v : Fin 4 → RatFunc K) (a i j : Fin 4) (ha : v a = 1)
    (hminor : ((rationalParameterJetMatrix v).submatrix id ![a, i, j]).det ≠ 0)
    (hspeed : T (f RatFunc.X) ≠ 0) :
    LinearIndependent F (normalCharacteristicMatrix T (fun k => f (v k))).row := by
  apply three_rows_independent_of_column_minor _ ![a, i, j]
  rw [rational_normal_jet_minor_transfer f T v a i j ha]
  exact mul_ne_zero ((map_ne_zero f).mpr hminor) (pow_ne_zero 3 hspeed)

end DimensionFourDependence
