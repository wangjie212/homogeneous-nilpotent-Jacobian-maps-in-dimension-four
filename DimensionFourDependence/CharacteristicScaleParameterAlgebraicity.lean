import DimensionFourDependence.ScaledRulingParameterAlgebraicity
import DimensionFourDependence.LineChartPivots

/-! # Both characteristic target parameters are algebraic over their actual output -/

namespace DimensionFourDependence

set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- A nonzero coordinate minor of the actual independent output
vectors recovers the pencil parameter from the original outputs.
The same minor then recovers the independent scale power. -/
theorem characteristic_scale_parameters_algebraic_of_original_output_values
    {D E G : Type*} [Field D] [Field E] [Field G] [Algebra D G] {m : ℕ}
    (τ : E →+* G) (hcoeff : ∀ b : E, IsAlgebraic D (τ b))
    (V W : Fin m → E) (hVW : LinearIndependent E ![V, W])
    (d : ℕ) (hd : 0 < d) (s t : G) (hs : s ≠ 0) (ht : t ≠ 0)
    (Y : Fin m → G)
    (hY : ∀ i, Y i = s ^ d * t ^ (d - 1) * (t * τ (V i) + τ (W i)))
    (houtput : ∀ i, IsAlgebraic D (Y i)) :
    IsAlgebraic D s ∧ IsAlgebraic D t := by
  obtain ⟨i, j, hij⟩ := independent_pair_exists_nonzero_coordinate_minor V W hVW
  let Δ := τ (V i) * τ (W j) - τ (V j) * τ (W i)
  have hΔ : Δ ≠ 0 := by
    simpa only [Δ, ← map_mul, ← map_sub] using (map_ne_zero τ).mpr hij
  have hΔalg : IsAlgebraic D Δ :=
    ((hcoeff (V i)).mul (hcoeff (W j))).sub ((hcoeff (V j)).mul (hcoeff (W i)))
  let A := Y i * τ (W j) - Y j * τ (W i)
  let B := τ (V i) * Y j - τ (V j) * Y i
  have hAalg : IsAlgebraic D A :=
    ((houtput i).mul (hcoeff (W j))).sub ((houtput j).mul (hcoeff (W i)))
  have hBalg : IsAlgebraic D B :=
    ((hcoeff (V i)).mul (houtput j)).sub ((hcoeff (V j)).mul (houtput i))
  have hB : B = s ^ d * t ^ (d - 1) * Δ := by
    dsimp only [B, Δ]
    rw [hY i, hY j]
    ring
  have hB0 : B ≠ 0 := by
    rw [hB]
    exact mul_ne_zero (mul_ne_zero (pow_ne_zero d hs) (pow_ne_zero (d - 1) ht)) hΔ
  have hA : A = t * B := by
    dsimp only [A, B]
    rw [hY i, hY j]
    ring
  have htalg : IsAlgebraic D t := by
    have he : t = A / B := by rw [hA, mul_div_cancel_right₀ _ hB0]
    rw [he]
    simpa only [div_eq_mul_inv] using hAalg.mul hBalg.inv
  have hspower : IsAlgebraic D (s ^ d) := by
    have he : s ^ d = B / (t ^ (d - 1) * Δ) := by
      rw [hB]
      field_simp [ht, hΔ]
    rw [he]
    simpa only [div_eq_mul_inv] using hBalg.mul ((htalg.pow (d - 1)).mul hΔalg).inv
  exact ⟨IsAlgebraic.of_pow hd hspower, htalg⟩

end DimensionFourDependence
