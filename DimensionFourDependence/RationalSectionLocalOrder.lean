import DimensionFourDependence.UnramifiedDivisorOrder

/-! # Rational-section orders in a chosen local frame

A local frame identifies a rational section with a rational function.
Another regular frame differs by a source-local unit, which has divisor
valuation one. Thus both the source order and its checked rational
pullback order are independent of that choice of local frame.
-/

namespace DimensionFourDependence

open scoped WithZero

variable {O F : Type*} [CommRing O] [IsDedekindDomain O] [Field F]
  [Algebra O F] [IsFractionRing O F]

/-- A regular unit used to change a local frame has zero divisor order. -/
theorem rational_section_local_frame_unit_value
    (v : IsDedekindDomain.HeightOneSpectrum O) (u : Oˣ) :
    v.valuation F (algebraMap O F (u : O)) = 1 := by
  apply v.valuation_eq_one_iff_notMem.mpr
  intro hu
  apply v.isPrime.ne_top
  exact Ideal.eq_top_of_isUnit_mem _ hu u.isUnit

/-- Multiplying a local rational-section coefficient by the regular
transition unit leaves its normalized divisor order unchanged. -/
theorem rational_section_local_frame_mul_unit
    (v : IsDedekindDomain.HeightOneSpectrum O) (u : Oˣ) (x : F) :
    v.valuation F (algebraMap O F (u : O) * x) = v.valuation F x := by
  rw [map_mul, rational_section_local_frame_unit_value, one_mul]

/-- The inverse local frame transition also leaves the order unchanged. -/
theorem rational_section_local_frame_div_unit
    (v : IsDedekindDomain.HeightOneSpectrum O) (u : Oˣ) (x : F) :
    v.valuation F (x / algebraMap O F (u : O)) = v.valuation F x := by
  rw [map_div₀, rational_section_local_frame_unit_value, div_one]

/-- The checked rational source-order equality applies to rational
sections in every compatible regular local frame. -/
theorem rational_section_pullback_order_change_frame
    {L : Type*} [Field L] (v : IsDedekindDomain.HeightOneSpectrum O)
    (w : Valuation L ℤᵐ⁰) (j : F →+* L)
    (horder : ∀ x : F, v.valuation F x = w (j x)) (u : Oˣ) (x : F) :
    w (j (algebraMap O F (u : O) * x)) = v.valuation F x := by
  rw [← horder]
  exact rational_section_local_frame_mul_unit v u x

end DimensionFourDependence
