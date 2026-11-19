import DimensionFourDependence.RankTwoIsotropicPlane

/-! # Two coordinate normalizations in a radial direction plane -/

namespace DimensionFourDependence

variable {F : Type*} [Field F] {n : ℕ}

/-- A zero coordinate and a unit coordinate distinguish a normalized
direction from a radial vector with nonzero coordinate in the zero slot. -/
theorem normalized_radial_direction_independent
    (Y Z : Fin n → F) (a b : Fin n) (hYa : Y a ≠ 0) (hZa : Z a = 0) (hZb : Z b = 1) :
    LinearIndependent F ![Y, Z] := by
  apply Fintype.linearIndependent_iff.mpr
  intro c hc i
  have hca := congrFun hc a
  have hcb := congrFun hc b
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hca hcb
  have hc0 : c 0 = 0 := by
    rw [hZa, mul_zero, add_zero] at hca
    exact (mul_eq_zero.mp hca).resolve_right hYa
  have hc1 : c 1 = 0 := by
    simpa only [hc0, zero_mul, zero_add, hZb, mul_one] using hcb
  fin_cases i <;> assumption

/-- A vector in the radial direction plane with zero entries in both
normalizing slots is zero. -/
theorem normalized_radial_plane_vector_zero
    (Y Z u : Fin n → F) (a b : Fin n) (hYa : Y a ≠ 0) (hZa : Z a = 0) (hZb : Z b = 1)
    (hu : u ∈ Submodule.span F (Set.range ![Y, Z])) (hua : u a = 0) (hub : u b = 0) : u = 0 := by
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun (R := F)).mp hu
  have hca := congrFun hc a
  have hcb := congrFun hc b
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hca hcb
  have hc0 : c 0 = 0 := by
    rw [hZa, mul_zero, add_zero, hua] at hca
    exact (mul_eq_zero.mp hca).resolve_right hYa
  have hc1 : c 1 = 0 := by
    simpa only [hc0, zero_mul, zero_add, hZb, mul_one, hub] using hcb
  have hz : c = 0 := by funext i; fin_cases i <;> assumption
  rw [hz] at hc
  simpa only [Pi.zero_apply, zero_smul, Finset.sum_const_zero] using hc.symm

end DimensionFourDependence
