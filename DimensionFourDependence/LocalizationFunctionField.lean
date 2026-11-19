import DimensionFourDependence.Defs
import Mathlib.RingTheory.Localization.LocalizationLocalization

/-! # Actual function fields of coordinate localizations

A domain and any injective localization have the same function field.
This direction starts with the fraction field of the localized ring and
proves that it is also a fraction field of the original coordinate ring,
using their given compatible algebra structures.
-/

namespace DimensionFourDependence

variable {R B L : Type*} [CommRing R] [IsDomain R] [CommRing B] [IsDomain B]
  [CommRing L] [Algebra R B] [FaithfulSMul R B]
  [Algebra R L] [Algebra B L] [IsScalarTower R B L] [IsFractionRing B L]

/-- The fraction field of an injective coordinate localization is the
original coordinate algebra's fraction field with its actual inclusion. -/
theorem source_localization_same_fraction_field
    (M : Submonoid R) [IsLocalization M B] : IsFractionRing R L := by
  have he : (nonZeroDivisors B).comap (algebraMap R B) = nonZeroDivisors R := by
    ext r
    simp only [Submonoid.mem_comap, mem_nonZeroDivisors_iff_ne_zero]
    constructor
    · intro hr hz
      apply hr
      rw [hz, map_zero]
    · intro hr hz
      apply hr
      exact FaithfulSMul.algebraMap_injective R B (by simpa using hz)
  have h : IsLocalization ((nonZeroDivisors B).comap (algebraMap R B)) L :=
    IsLocalization.localization_localization_isLocalization_of_has_all_units M (nonZeroDivisors B) L
      (fun _ hx => hx.mem_nonZeroDivisors)
  rwa [he] at h

end DimensionFourDependence
