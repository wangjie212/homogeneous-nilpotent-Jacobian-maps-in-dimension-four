import DimensionFourDependence.Defs
import Mathlib.RingTheory.OrderOfVanishing.Noetherian

/-! # A DVR vanishing-order bound is bounded by its principal quotient length -/

namespace DimensionFourDependence

variable {B : Type*} [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]

/-- A regular function in the ath maximal-ideal power has principal
quotient length at least a. This uses the actual local element, including
the zero element, before any finiteness assertion on its quotient. -/
theorem dvr_power_order_le_quotient_length
    (z : B) (a : ℕ) (h : z ∈ (IsLocalRing.maximalIdeal B) ^ a) :
    (a : ENat) ≤ Module.length B (B ⧸ Ideal.span {z}) := by
  have hle : Ideal.span {z} ≤ (IsLocalRing.maximalIdeal B) ^ a :=
    Ideal.span_le.mpr (by simpa using h)
  rw [← IsDiscreteValuationRing.length_quotient_pow_maximalIdeal B a,
    Module.length_quotient, Module.length_quotient]
  exact Order.coheight_anti hle

/-- For a nonzero regular function the quotient length is finite,
so its actual integer multiplicity bounds every maximal-ideal order. -/
theorem dvr_power_order_le_quotient_length_toNat
    (z : B) (hz : z ≠ 0) (a : ℕ) (h : z ∈ (IsLocalRing.maximalIdeal B) ^ a) :
    a ≤ (Module.length B (B ⧸ Ideal.span {z})).toNat := by
  have hfinite : Module.length B (B ⧸ Ideal.span {z}) ≠ ⊤ :=
    Module.length_ne_top_iff.mpr
      (isFiniteLength_quotient_span_singleton B (mem_nonZeroDivisors_iff_ne_zero.mpr hz))
  simpa only [ENat.toNat_natCast] using
    ENat.toNat_le_toNat (dvr_power_order_le_quotient_length z a h) hfinite

end DimensionFourDependence
