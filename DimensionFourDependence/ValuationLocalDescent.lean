import DimensionFourDependence.Defs
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.LocalRing.RingHom.Basic

/-! # Regular source fractions descend through dominating local extensions

A valuation-ring source fraction cannot acquire regularity in a local
extension dominating that valuation ring: a source pole would make its
regular inverse both a nonunit downstairs and a unit upstairs. This is
the valuative input for recovering horizontal parameter embeddings from
the contraction of a curve prime, rather than assuming such embeddings.
-/

namespace DimensionFourDependence

variable {A B F L : Type*} [CommRing A] [IsDomain A] [ValuationRing A]
  [CommRing B] [Field F] [Field L]
  [Algebra A F] [IsFractionRing A F] [Algebra A B] [Algebra F L]
  [Algebra A L] [IsScalarTower A F L] [Algebra B L] [IsScalarTower A B L]
  [FaithfulSMul B L] [IsLocalHom (algebraMap A B)]

/-- A source rational function regular in a dominating local extension
is already regular in the source valuation ring. -/
theorem valuation_source_fraction_regular_of_local_extension
    (x : F) (b : B) (hx : algebraMap F L x = algebraMap B L b) :
    IsLocalization.IsInteger A x := by
  by_cases hx0 : x = 0
  · exact ⟨0, by simp [hx0]⟩
  rcases ValuationRing.isInteger_or_isInteger A x with hreg | ⟨a, ha⟩
  · exact hreg
  have hab : algebraMap A B a * b = 1 := by
    apply FaithfulSMul.algebraMap_injective B L
    rw [map_mul, map_one, ← IsScalarTower.algebraMap_apply A B L,
      IsScalarTower.algebraMap_apply A F L, ha, ← hx, map_inv₀]
    exact inv_mul_cancel₀ (by simpa using hx0)
  have huB : IsUnit (algebraMap A B a) := isUnit_iff_exists_inv.mpr ⟨b, hab⟩
  have huA : IsUnit a := isUnit_of_map_unit (algebraMap A B) a huB
  refine ⟨(huA.unit⁻¹ : Aˣ), ?_⟩
  apply mul_right_cancel₀ (inv_ne_zero hx0)
  calc
    algebraMap A F (↑(huA.unit⁻¹) : A) * x⁻¹ =
        algebraMap A F (↑(huA.unit⁻¹) : A) * algebraMap A F (↑huA.unit : A) := by
      rw [huA.unit_spec, ha]
    _ = 1 := by rw [← map_mul]; simp
    _ = x * x⁻¹ := (mul_inv_cancel₀ hx0).symm

variable {C : Type*} [Field C] [Algebra C F] [Algebra C B] [Algebra C L]
  [IsScalarTower C F L] [IsScalarTower C B L]

include B L in
/-- A coefficient field contained in a dominating local extension and
in the source function field already lies in the source valuation ring. -/
theorem valuation_source_contains_coefficient_field (c : C) :
    IsLocalization.IsInteger A (algebraMap C F c) := by
  apply valuation_source_fraction_regular_of_local_extension (A := A) (B := B) (F := F) (L := L)
    (b := algebraMap C B c)
  rw [← IsScalarTower.algebraMap_apply C F L, ← IsScalarTower.algebraMap_apply C B L]

end DimensionFourDependence
