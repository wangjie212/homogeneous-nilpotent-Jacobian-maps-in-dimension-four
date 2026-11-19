import DimensionFourDependence.ScaledPlaneVertexTargetFibers
import DimensionFourDependence.AlgebraicRationalFunctionImages

/-! # Exact scaled ruling target values force both parameters to be algebraic over the output -/

namespace DimensionFourDependence

open Matrix

set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The exact two dual output pairings recover the independent scale
power and ruling parameter. Hence algebraic coefficient images and
actual output values make both parameters algebraic over the output. -/
theorem scaled_ruling_parameters_algebraic_of_original_output_values
    {D E G : Type*} [Field D] [Field E] [Field G] [Algebra D G] {m : ℕ}
    (τ : E →+* G) (hcoeff : ∀ b : E, IsAlgebraic D (τ b))
    (s n bS bN : Fin m → E)
    (hsS : s ⬝ᵥ bS = 1) (hnS : n ⬝ᵥ bS = 0)
    (hsN : s ⬝ᵥ bN = 0) (hnN : n ⬝ᵥ bN = 1)
    (a : E) (ha : a ≠ 0) (d : ℕ) (hd : 0 < d)
    (r level : G) (hr : r ≠ 0) (Y : Fin m → G)
    (hY : ∀ i, Y i = r ^ d * (τ (a ^ d * bS i) + level * τ (bN i)))
    (houtput : ∀ i, IsAlgebraic D (Y i)) :
    IsAlgebraic D r ∧ IsAlgebraic D level := by
  have hsS' : (fun i => τ (s i)) ⬝ᵥ (fun i => τ (bS i)) = 1 := by
    simpa only [dotProduct, map_sum, map_mul, map_one] using congrArg τ hsS
  have hnS' : (fun i => τ (n i)) ⬝ᵥ (fun i => τ (bS i)) = 0 := by
    simpa only [dotProduct, map_sum, map_mul, map_zero] using congrArg τ hnS
  have hsN' : (fun i => τ (s i)) ⬝ᵥ (fun i => τ (bN i)) = 0 := by
    simpa only [dotProduct, map_sum, map_mul, map_zero] using congrArg τ hsN
  have hnN' : (fun i => τ (n i)) ⬝ᵥ (fun i => τ (bN i)) = 1 := by
    simpa only [dotProduct, map_sum, map_mul, map_one] using congrArg τ hnN
  have hpair := dual_scaled_target_pairings (fun i => τ (s i)) (fun i => τ (n i))
    (fun i => τ (bS i)) (fun i => τ (bN i)) hsS' hnS' hsN' hnN' (τ (a ^ d)) level
  have hY' : Y = r ^ d • (fun i => τ (a ^ d) * τ (bS i) + level * τ (bN i)) := by
    funext i
    simpa only [Pi.smul_apply, smul_eq_mul, map_mul] using hY i
  have hsY : (fun i => τ (s i)) ⬝ᵥ Y = r ^ d * τ (a ^ d) := by
    rw [hY', dotProduct_smul, hpair.1]
    rfl
  have hnY : (fun i => τ (n i)) ⬝ᵥ Y = r ^ d * level := by
    rw [hY', dotProduct_smul, hpair.2]
    rfl
  have hsum (c : Fin m → E) : IsAlgebraic D ((fun i => τ (c i)) ⬝ᵥ Y) := by
    exact (IsIntegral.sum _ (fun i _ => (hcoeff (c i)).isIntegral.mul (houtput i).isIntegral)).isAlgebraic
  have hscale : IsAlgebraic D (r ^ d) := by
    have he : r ^ d = ((fun i => τ (s i)) ⬝ᵥ Y) * (τ (a ^ d))⁻¹ := by
      rw [hsY]
      rw [mul_assoc, mul_inv_cancel₀ ((map_ne_zero τ).mpr (pow_ne_zero d ha)), mul_one]
    rw [he]
    exact (hsum s).mul (hcoeff (a ^ d)).inv
  refine ⟨IsAlgebraic.of_pow hd hscale, ?_⟩
  have he : level = ((fun i => τ (n i)) ⬝ᵥ Y) * (r ^ d)⁻¹ := by
    rw [hnY]
    field_simp [hr]
  rw [he]
  exact (hsum n).mul hscale.inv

end DimensionFourDependence
