import DimensionFourDependence.ResidueParameterField

/-! # A nonzero regular zero of a local pencil is transcendental over its constants -/

namespace DimensionFourDependence

variable {E A F : Type*} [Field E] [CommRing A] [IsDomain A] [IsLocalRing A]
  [Field F] [Algebra E A] [Algebra A F] [IsFractionRing A F]
  [Algebra E F] [IsScalarTower E A F]

/-- Dividing a nonzero local zero by a regular unit retains a
nonzero local zero. Its fraction-field value is transcendental over
the coefficient field contained in that same local ring. -/
theorem local_unit_quotient_has_regular_nonzero_zero_and_transcendental_value
    (u v : A) (hu : u ≠ 0) (hzero : u ∈ IsLocalRing.maximalIdeal A) (hv : IsUnit v) :
    ∃ f : A, f ≠ 0 ∧ f ∈ IsLocalRing.maximalIdeal A ∧
      algebraMap A F f = algebraMap A F u / algebraMap A F v ∧
      Transcendental E (algebraMap A F u / algebraMap A F v) := by
  obtain ⟨b, hb⟩ := isUnit_iff_exists_inv.mp hv
  have hvF : algebraMap A F v ≠ 0 := (hv.map (algebraMap A F)).ne_zero
  have hbF : algebraMap A F b = (algebraMap A F v)⁻¹ := by
    apply mul_left_cancel₀ hvF
    rw [← map_mul, hb, map_one, mul_inv_cancel₀ hvF]
  let f := u * b
  have hfvalue : algebraMap A F f = algebraMap A F u / algebraMap A F v := by
    change algebraMap A F (u * b) = _
    rw [map_mul, hbF, div_eq_mul_inv]
  have hf : f ≠ 0 := by
    intro hz
    have he := congrArg (algebraMap A F) hz
    rw [hfvalue, map_zero] at he
    exact div_ne_zero ((map_ne_zero_iff _ (IsFractionRing.injective A F)).mpr hu) hvF he
  have hfzero : f ∈ IsLocalRing.maximalIdeal A :=
    (IsLocalRing.maximalIdeal A).mul_mem_right b hzero
  have ht : Transcendental E (algebraMap A F f) :=
    (transcendental_algebraMap_iff (IsFractionRing.injective A F)).mpr
      (local_nonzero_nonunit_transcendental f hf hfzero)
  exact ⟨f, hf, hfzero, hfvalue, hfvalue ▸ ht⟩

end DimensionFourDependence
