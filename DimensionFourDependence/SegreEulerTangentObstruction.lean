import DimensionFourDependence.SegreEulerDerivativeProfiles

/-! # Euler weights construct the homogeneous profiles in the ruling obstruction -/

namespace DimensionFourDependence

open Matrix

set_option maxHeartbeats 3000000

variable {K F : Type*} [Field K] [Field F] [Algebra K F] [CharZero F]

/-- Positive primitive degree, the actual Euler equations and actual
ruling dominance construct all normalized profiles and their nonzero
Wronskian. They therefore exclude the complete residue chart action
without any supplied homogeneous profile formulas. -/
theorem segre_ruling_euler_chart_not_nilpotent
    (Dx Dy : Derivation K F F) (x y f g a : F) (hx : x ≠ 0)
    (hDyx : Dy x = 0) (hDyy : Dy y = 1)
    (d j : ℕ) (hdegree : 2 * j < d)
    (hfEuler : x * Dx f + y * Dy f = ((d : F) - (j : F)) * f)
    (hgEuler : x * Dx g + y * Dy g = ((d : F) - (j : F)) * g)
    (haEuler : x * Dx a + y * Dy a = -a)
    (hdom : f * Dy g - g * Dy f ≠ 0) :
    ¬IsNilpotent (segreRulingChartTangentMatrix (j : F) f g (Dx f) (Dy f) (Dx g) (Dy g)
      a (Dx a) (Dy a) x⁻¹ (y / x)) := by
  intro hN
  let k := d - j
  have hk : 0 < k := by dsimp only [k]; omega
  have hkcast : (k : F) = (d : F) - (j : F) := Nat.cast_sub (by omega)
  have hfE : x * Dx f + y * Dy f = (k : F) * f := by rw [hkcast]; exact hfEuler
  have hgE : x * Dx g + y * Dy g = (k : F) * g := by rw [hkcast]; exact hgEuler
  obtain ⟨hf0, hfy, hfx⟩ := segre_euler_weight_constructs_function_profile Dx Dy x y f hx hDyx k hk hfE
  obtain ⟨hg0, hgy, hgx⟩ := segre_euler_weight_constructs_function_profile Dx Dy x y g hx hDyx k hk hgE
  obtain ⟨ha0, hay, hax⟩ := segre_euler_weight_constructs_slope_profile Dx Dy x y a hx hDyx haEuler
  have hs := segre_radial_derivation_parameter Dy x y hx hDyx hDyy
  have hdomN := segre_normalized_profile_wronskian_ne_zero Dy x f g hx hDyx k hdom
  have hnot := dominant_segre_homogeneous_chart_not_nilpotent
    (x • Dy) (y / x) hs d j hdegree (f / x ^ k) (g / x ^ k) (x * a) x (x ^ (k - 1))
      hx (pow_ne_zero _ hx) hdomN
  apply hnot
  simpa only [← hkcast, hf0, hg0, hfy, hfx, hgy, hgx, ha0, hay, hax] using hN

end DimensionFourDependence
