import DimensionFourDependence.Defs
import Mathlib.RingTheory.Valuation.LocalSubring

/-! # Integrality detected by actual valuation subrings of the function field

The integral closure is separated from any element outside it by a
valuation subring containing the original coefficient ring. Consequently
regularity in every such valuation ring constructs an integral equation.
-/

namespace DimensionFourDependence

variable {R L : Type*} [CommRing R] [Field L] [Algebra R L]

/-- An integral value belongs to every actual function-field valuation
subring containing the images of its coefficient ring. -/
theorem integral_value_mem_valuationSubring
    (z : L) (hz : IsIntegral R z) (V : ValuationSubring L)
    (hR : ∀ r : R, algebraMap R L r ∈ V) : z ∈ V := by
  let : IsIntegrallyClosedIn V.toSubring L := inferInstanceAs (IsIntegrallyClosedIn V L)
  have hle : (integralClosure R L).toSubring ≤ V.toSubring :=
    Subring.integralClosure_le_iff.mpr hR
  exact hle hz

/-- Membership in every actual function-field valuation subring
containing the coefficient ring constructs integrality over that ring. -/
theorem isIntegral_of_mem_all_valuationSubrings
    (z : L) (h : ∀ V : ValuationSubring L,
      (∀ r : R, algebraMap R L r ∈ V) → z ∈ V) : IsIntegral R z := by
  by_contra hz
  have hz' : z ∉ (integralClosure R L).toSubring := hz
  obtain ⟨V, hV, hzV⟩ := Subring.exists_le_valuationSubring_of_isIntegrallyClosedIn hz'
  apply hzV
  exact h V (fun r => hV ((integralClosure R L).algebraMap_mem r))

end DimensionFourDependence
