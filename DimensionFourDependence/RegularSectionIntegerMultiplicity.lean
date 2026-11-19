import DimensionFourDependence.SchemeRegularOrderBounds
import DimensionFourDependence.NormalDivisorStalkDvr

/-! # A regular section's bounded local powers give its actual integer multiplicity -/

namespace DimensionFourDependence

open AlgebraicGeometry IsDiscreteValuationRing

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000

/-- At a divisor DVR, bounding every maximal-ideal power of a nonzero
regular coefficient bounds its actual integer scheme order, which is
nonnegative. No uniformizer or integer multiplicity is supplied. -/
theorem scheme_regular_integer_multiplicity_bounded
    {X : Scheme} [IsIntegral X] [IsLocallyNoetherian X]
    (y : X) (hy : Order.coheight y = 1) [IsDiscreteValuationRing (X.presheaf.stalk y)]
    (z : X.presheaf.stalk y) (hz : z ≠ 0) (D : ℕ)
    (hbound : ∀ a : ℕ, z ∈ (IsLocalRing.maximalIdeal (X.presheaf.stalk y)) ^ a → a ≤ D) :
    0 ≤ X.ord (algebraMap (X.presheaf.stalk y) X.functionField z) y ∧
      X.ord (algebraMap (X.presheaf.stalk y) X.functionField z) y ≤ (D : ℤ) := by
  obtain ⟨π, hπ⟩ := exists_irreducible (X.presheaf.stalk y)
  obtain ⟨n, v, rfl⟩ := eq_unit_mul_pow_irreducible hz hπ
  rw [scheme_order_unit_mul_uniformizer_pow y hy π hπ v n]
  refine ⟨Int.natCast_nonneg n, ?_⟩
  apply Int.ofNat_le.mpr
  apply hbound n
  apply Ideal.mul_mem_left
  apply Ideal.pow_mem_pow
  rw [hπ.maximalIdeal_eq]
  exact Ideal.mem_span_singleton.mpr (dvd_refl π)

end DimensionFourDependence
