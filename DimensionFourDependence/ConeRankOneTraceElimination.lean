import DimensionFourDependence.Nilpotent

/-! # Eliminating the radial derivative in the fixed cone Jacobian

The fixed-parameter part has rank one in its upper three rows and zero
last column. The difference between squared trace and trace of the square
eliminates the radial parameter derivative and constructs a triangular
tangent equation. This uses only the first two nilpotence consequences.
-/

namespace DimensionFourDependence

open Matrix

set_option maxHeartbeats 3000000

variable {R : Type*} [CommRing R]

/-- The actual shape of the four-variable Jacobian on the cone chart,
with the fixed-parameter and parameter-gradient contributions explicit. -/
def coneRankOneChartMatrix (d : R) (a c b : Fin 3 → R) (L q : R) (g : Fin 4 → R) :
    Matrix (Fin 4) (Fin 4) R :=
  !![c 0 * g 0, d * a 0 + c 0 * g 1, c 0 * g 2, c 0 * g 3;
     c 1 * g 0, d * a 1 + c 1 * g 1, c 1 * g 2, c 1 * g 3;
     c 2 * g 0, d * a 2 + c 2 * g 1, c 2 * g 2, c 2 * g 3;
     b 0 + q * g 0, (d - 1) * L + b 1 + q * g 1, b 2 + q * g 2, q * g 3]

/-- Squared trace minus trace of the square is twice the full
triangular tangent expression, with its radial component eliminated. -/
theorem cone_chart_trace_square_elimination_identity
    (d : R) (a c b : Fin 3 → R) (L q : R) (g : Fin 4 → R) :
    (Matrix.trace (coneRankOneChartMatrix d a c b L q g)) ^ 2 -
      Matrix.trace (coneRankOneChartMatrix d a c b L q g * coneRankOneChartMatrix d a c b L q g) =
    2 * (d * (a 1 * c 0 - c 1 * a 0) * g 0 +
      d * (a 1 * c 2 - c 1 * a 2) * g 2 +
      (d * a 1 * q - (b 0 * c 0 + b 1 * c 1 + b 2 * c 2) - (d - 1) * L * c 1) * g 3) := by
  simp [Matrix.trace, Matrix.diag, Matrix.mul_apply, coneRankOneChartMatrix, Fin.sum_univ_succ]
  ring

/-- The first two nilpotence trace identities construct the entire
triangular tangent equation without a supplied tangent or slope. -/
theorem cone_chart_two_zero_traces_construct_triangular_tangency
    [IsDomain R] [CharZero R]
    (d : R) (a c b : Fin 3 → R) (L q : R) (g : Fin 4 → R)
    (htrace : Matrix.trace (coneRankOneChartMatrix d a c b L q g) = 0)
    (hsquare : Matrix.trace
      (coneRankOneChartMatrix d a c b L q g * coneRankOneChartMatrix d a c b L q g) = 0) :
    d * (a 1 * c 0 - c 1 * a 0) * g 0 +
      d * (a 1 * c 2 - c 1 * a 2) * g 2 +
      (d * a 1 * q - (b 0 * c 0 + b 1 * c 1 + b 2 * c 2) - (d - 1) * L * c 1) * g 3 = 0 := by
  have he := cone_chart_trace_square_elimination_identity d a c b L q g
  rw [htrace, hsquare, zero_pow (by decide : (2 : ℕ) ≠ 0), sub_self] at he
  exact (mul_eq_zero.mp he.symm).resolve_left (by norm_num)

/-- Nilpotence itself supplies both zero traces required by the
constructed triangular tangent equation. -/
theorem nilpotent_cone_chart_constructs_triangular_tangency
    [IsDomain R] [CharZero R]
    (d : R) (a c b : Fin 3 → R) (L q : R) (g : Fin 4 → R)
    (hN : IsNilpotent (coneRankOneChartMatrix d a c b L q g)) :
    d * (a 1 * c 0 - c 1 * a 0) * g 0 +
      d * (a 1 * c 2 - c 1 * a 2) * g 2 +
      (d * a 1 * q - (b 0 * c 0 + b 1 * c 1 + b 2 * c 2) - (d - 1) * L * c 1) * g 3 = 0 := by
  apply cone_chart_two_zero_traces_construct_triangular_tangency
  · exact (Matrix.isNilpotent_trace_of_isNilpotent hN).eq_zero
  · obtain ⟨n, hn⟩ := hN
    have hpow : IsNilpotent (coneRankOneChartMatrix d a c b L q g *
        coneRankOneChartMatrix d a c b L q g) := by
      refine ⟨n, ?_⟩
      rw [← pow_two, ← pow_mul, Nat.mul_comm 2 n, pow_mul, hn, zero_pow (by decide : (2 : ℕ) ≠ 0)]
    exact (Matrix.isNilpotent_trace_of_isNilpotent hpow).eq_zero

end DimensionFourDependence
