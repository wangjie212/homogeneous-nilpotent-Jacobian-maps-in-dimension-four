import DimensionFourDependence.LocalizationDerivation

/-! # The localized derivative retains its exact original function-field realization -/

namespace DimensionFourDependence

set_option maxHeartbeats 3000000

variable {K R O F : Type*} [CommRing K] [CommRing R] [CommRing O] [Field F]
  [Algebra K R] [Algebra R O] [Algebra K O] [IsScalarTower K R O]
  [Algebra R F] [Algebra K F] [IsScalarTower K R F]
  (M : Submonoid R) [IsLocalization M O]

/-- Agreement on the original source ring implies agreement on every
localized fraction. The proof differentiates an actual denominator
identity and cancels its specified nonzero image in the containing field. -/
theorem localizationDerivation_compatible_field
    (D : Derivation K R R) (E : Derivation K F F) (φ : O →ₐ[R] F)
    (hbase : ∀ r : R, E (algebraMap R F r) = algebraMap R F (D r)) (v : O) :
    φ (localizationDerivation (S := O) M D v) = E (φ v) := by
  obtain ⟨⟨r, m⟩, he⟩ := IsLocalization.surj M v
  have hlocal := congrArg (localizationDerivation (S := O) M D) he
  rw [Derivation.leibniz, localizationDerivation_algebraMap, localizationDerivation_algebraMap] at hlocal
  simp only [smul_eq_mul] at hlocal
  have hL := congrArg φ hlocal
  simp only [map_add, map_mul, φ.commutes] at hL
  have hfield : φ v * algebraMap R F (m : R) = algebraMap R F r := by
    simpa only [map_mul, φ.commutes] using congrArg φ he
  have hE := congrArg E hfield
  rw [Derivation.leibniz, hbase (m : R), hbase r] at hE
  simp only [smul_eq_mul] at hE
  have hm : algebraMap R F (m : R) ≠ 0 := by
    have hu : IsUnit (algebraMap R F (m : R)) := by
      simpa only [φ.commutes] using (IsLocalization.map_units O m).map φ
    exact hu.ne_zero
  apply mul_left_cancel₀ hm
  linear_combination hL - hE

end DimensionFourDependence
