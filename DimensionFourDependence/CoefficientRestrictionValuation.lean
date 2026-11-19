import DimensionFourDependence.ValuationProjectiveHilbertSpecialization
import Mathlib.RingTheory.Valuation.ValuationRing

/-! # Restricting an actual source valuation ring to a specified coefficient field -/

namespace DimensionFourDependence

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000

variable {A F : Type*} [CommRing A] [IsDomain A] [ValuationRing A]
  [Field F] [Algebra A F] [IsFractionRing A F]
  (C : Type*) [Field C] [Algebra C F]

/-- The coefficient valuation consists exactly of those specified
coefficient values regular in the actual source valuation ring. -/
noncomputable def coefficientRestrictionValuationSubring : ValuationSubring C :=
  (ValuationRing.valuation A F).valuationSubring.comap (algebraMap C F)

/-- Membership is actual regularity of the same coefficient value
in the original source field. -/
theorem coefficientRestrictionValuationSubring_mem_iff (c : C) :
    c ∈ coefficientRestrictionValuationSubring (A := A) (F := F) C ↔
      ∃ a : A, algebraMap A F a = algebraMap C F c := by
  exact ValuationRing.mem_integer_iff A F (algebraMap C F c)

/-- The coefficient valuation embeds in the original source local
ring through the regular representatives of its specified field values. -/
noncomputable def coefficientRestrictionLocalHom :
    coefficientRestrictionValuationSubring (A := A) (F := F) C →+* A := by
  let V := coefficientRestrictionValuationSubring (A := A) (F := F) C
  let f : V → A := fun c => Classical.choose
    ((coefficientRestrictionValuationSubring_mem_iff (A := A) (F := F) C c).mp c.property)
  have hf (c : V) : algebraMap A F (f c) = algebraMap C F (c : C) := Classical.choose_spec
    ((coefficientRestrictionValuationSubring_mem_iff (A := A) (F := F) C c).mp c.property)
  exact
    { toFun := f
      map_zero' := by apply IsFractionRing.injective A F; simp only [hf, ZeroMemClass.coe_zero, map_zero]
      map_one' := by apply IsFractionRing.injective A F; simp only [hf, OneMemClass.coe_one, map_one]
      map_add' := by
        intro c b
        apply IsFractionRing.injective A F
        simp only [hf, AddMemClass.coe_add, map_add]
      map_mul' := by
        intro c b
        apply IsFractionRing.injective A F
        simp only [hf, MulMemClass.coe_mul, map_mul] }

/-- The local coefficient embedding preserves the entire original
coefficient-field realization, not just its parameter generator. -/
theorem coefficientRestrictionLocalHom_source
    (c : coefficientRestrictionValuationSubring (A := A) (F := F) C) :
    algebraMap A F (coefficientRestrictionLocalHom (A := A) (F := F) C c) = algebraMap C F (c : C) :=
  Classical.choose_spec ((coefficientRestrictionValuationSubring_mem_iff (A := A) (F := F) C c).mp c.property)

/-- The coefficient valuation local map is local: its units are
exactly the coefficient elements whose inverses are regular in A. -/
theorem coefficientRestrictionLocalHom_isLocalHom :
    IsLocalHom (coefficientRestrictionLocalHom (A := A) (F := F) C) := by
  constructor
  intro c hc
  let f := coefficientRestrictionLocalHom (A := A) (F := F) C
  obtain ⟨b, hb⟩ := isUnit_iff_exists_inv.mp hc
  have hcF : algebraMap C F (c : C) ≠ 0 := by
    rw [← coefficientRestrictionLocalHom_source]
    exact (hc.map (algebraMap A F)).ne_zero
  have hc0 : (c : C) ≠ 0 := (map_ne_zero_iff _ (algebraMap C F).injective).mp hcF
  have hbF : algebraMap A F b = algebraMap C F ((c : C)⁻¹) := by
    apply mul_left_cancel₀ hcF
    rw [← coefficientRestrictionLocalHom_source (A := A) (F := F) C c,
      ← map_mul, hb, map_one, map_inv₀, coefficientRestrictionLocalHom_source,
      mul_inv_cancel₀ hcF]
  have hinv : (c : C)⁻¹ ∈ coefficientRestrictionValuationSubring (A := A) (F := F) C :=
    (coefficientRestrictionValuationSubring_mem_iff (A := A) (F := F) C _).mpr ⟨b, hbF⟩
  apply isUnit_iff_exists_inv.mpr
  refine ⟨⟨(c : C)⁻¹, hinv⟩, ?_⟩
  apply Subtype.ext
  exact mul_inv_cancel₀ hc0

/-- Restricting the valuation constructs the compatible embedding
of its own residue field into the actual source residue field. -/
noncomputable def coefficientRestrictionResidueHom :
    IsLocalRing.ResidueField (coefficientRestrictionValuationSubring (A := A) (F := F) C) →+*
      IsLocalRing.ResidueField A := by
  letI := coefficientRestrictionLocalHom_isLocalHom (A := A) (F := F) C
  exact IsLocalRing.ResidueField.map (coefficientRestrictionLocalHom (A := A) (F := F) C)

/-- The residue embedding uses exactly the residue of each regular
source coefficient value. -/
theorem coefficientRestrictionResidueHom_residue
    (c : coefficientRestrictionValuationSubring (A := A) (F := F) C) :
    coefficientRestrictionResidueHom (A := A) (F := F) C (IsLocalRing.residue _ c) =
      IsLocalRing.residue A (coefficientRestrictionLocalHom (A := A) (F := F) C c) := rfl

end DimensionFourDependence
