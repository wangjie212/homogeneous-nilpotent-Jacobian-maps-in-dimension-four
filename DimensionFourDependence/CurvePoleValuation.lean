import DimensionFourDependence.ImageIsotropicLine
import Mathlib.RingTheory.Valuation.LocalSubring

/-! # Valuation poles of nonconstant curve functions

A transcendental element is outside the integral closure of the constants.
The valuative description of integral closure supplies a valuation subring
containing all constants and excluding that element. No normalization of
the curve or choice of a discrete uniformizer is required.
-/

namespace DimensionFourDependence

variable {E F : Type*} [Field E] [Field F] [Algebra E F]

/-- Every transcendental function has a valuation pole over its constants. -/
theorem transcendental_has_valuation_pole (x : F) (hx : Transcendental E x) :
    ∃ V : ValuationSubring F, (∀ c : E, algebraMap E F c ∈ V) ∧ x ∉ V := by
  let R : Subring F := (integralClosure E F).toSubring
  have hxR : x ∉ R := by
    intro h
    exact hx (show IsIntegral E x from h).isAlgebraic
  obtain ⟨V, hV, hxV⟩ := Subring.exists_le_valuationSubring_of_isIntegrallyClosedIn hxR
  exact ⟨V, (fun c => hV ((integralClosure E F).algebraMap_mem c)), hxV⟩

/-- The same pole in the multiplicative valuation convention: its value is greater than one. -/
theorem transcendental_has_valuation_pole_gt_one (x : F) (hx : Transcendental E x) :
    ∃ V : ValuationSubring F, (∀ c : E, algebraMap E F c ∈ V) ∧ 1 < V.valuation x := by
  obtain ⟨V, hV, hxV⟩ := transcendental_has_valuation_pole x hx
  exact ⟨V, hV, lt_of_not_ge (fun h => hxV ((V.valuation_le_one_iff x).mp h))⟩

/-- Over algebraically closed constants, failure to be a scalar gives such a pole. -/
theorem nonscalar_has_valuation_pole [IsAlgClosed E] (x : F)
    (hx : ¬ ∃ c : E, algebraMap E F c = x) :
    ∃ V : ValuationSubring F, (∀ c : E, algebraMap E F c ∈ V) ∧ 1 < V.valuation x := by
  apply transcendental_has_valuation_pole_gt_one x
  intro hAlg
  have hm : x ∈ algebraicClosure E F := mem_algebraicClosure_iff.mpr hAlg
  have hb : algebraicClosure E F = ⊥ := IntermediateField.eq_bot_of_isAlgClosed_of_isAlgebraic _
  rw [hb] at hm
  exact hx hm

end DimensionFourDependence
