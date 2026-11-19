import DimensionFourDependence.FullBasisPartials
import DimensionFourDependence.BinaryOutputPartialConstants

/-! # Common constants of the slice and transverse partials -/

namespace DimensionFourDependence

open Matrix

universe u
set_option maxHeartbeats 2650000

variable {K F : Type u} [Field K] [CharZero K] [Field F] [Algebra K F]

/-- Two independent coordinate partials in a three-dimensional
function field have joint constants algebraic over the remaining
coordinate. A relatively closed coordinate gives the precise subfield. -/
theorem ternary_parameter_joint_constants_mem_closed_parameter_field
    (x r s : F) (hB : IsTranscendenceBasis K (![x, r, s] : Fin 3 → F))
    (htr : Algebra.trdeg K F ≤ 3)
    (hR : algebraicClosure (IntermediateField.adjoin K {r}) F = ⊥)
    (v : F) (hx : fullBasisPartial ![x, r, s] hB 0 v = 0)
    (hs : fullBasisPartial ![x, r, s] hB 2 v = 0) : v ∈ IntermediateField.adjoin K {r} := by
  let Y : Fin 2 → F := ![r, s]
  let D := fullBasisPartial ![x, r, s] hB 0
  let E := fullBasisPartial ![x, r, s] hB 2
  have hY : AlgebraicIndependent K Y := by
    let j : Fin 2 → Fin 3 := Fin.succ
    have he : ( (![x, r, s] : Fin 3 → F) ∘ j) = Y := by
      funext i
      fin_cases i <;> rfl
    rw [← he]
    exact hB.1.comp j (Fin.succ_injective 2)
  have hDx : D x = 1 := by
    change D ((![x, r, s] : Fin 3 → F) 0) = _
    rw [show D = fullBasisPartial ![x, r, s] hB 0 from rfl, fullBasisPartial_coordinate]
    rfl
  have hD : D ≠ 0 := by
    intro h
    rw [h, Derivation.zero_apply] at hDx
    exact zero_ne_one hDx
  have hDY (i : Fin 2) : D (Y i) = 0 := by
    fin_cases i
    · change fullBasisPartial ![x, r, s] hB 0 ((![x, r, s] : Fin 3 → F) 1) = _
      rw [fullBasisPartial_coordinate]
      rfl
    · change fullBasisPartial ![x, r, s] hB 0 ((![x, r, s] : Fin 3 → F) 2) = _
      rw [fullBasisPartial_coordinate]
      rfl
  have hYtr : Algebra.trdeg (IntermediateField.adjoin K (Set.range Y)) F ≤ 1 := by
    apply relative_trdeg_le_one_of_independent_outputs Y hY
    convert htr using 1
    norm_num
  let L := coefficientField (K := K) Y
  have hv : v ∈ L := (vertical_constant_iff_mem_coefficient_field Y D hD hDY hYtr v).mp hx
  let w : L := ⟨v, hv⟩
  let : IsScalarTower K L F := coefficientFieldScalarTower Y
  have he : E.compAlgebraMap L = coefficientAmbientPartial Y hY 1 := by
    apply coefficient_ambient_derivation_ext Y
    intro i
    have hi : (coefficientPartial Y hY 1 (coefficientCoordinate Y i) : F) =
        if i = 1 then 1 else 0 := by
      rw [show coefficientPartial Y hY 1 (coefficientCoordinate Y i) = _ from
        coefficientPartial_coordinate Y hY 1 i]
      split <;> rfl
    change E (Y i) = (coefficientPartial Y hY 1 (coefficientCoordinate Y i) : F)
    rw [hi]
    fin_cases i
    · change fullBasisPartial ![x, r, s] hB 2 ((![x, r, s] : Fin 3 → F) 1) = _
      rw [fullBasisPartial_coordinate]
      rfl
    · change fullBasisPartial ![x, r, s] hB 2 ((![x, r, s] : Fin 3 → F) 2) = _
      rw [fullBasisPartial_coordinate]
      rfl
  have hz : coefficientPartial Y hY 1 w = 0 := by
    apply Subtype.val_injective
    exact (DFunLike.congr_fun he w).symm.trans hs
  have halg := second_coefficientPartial_zero_isAlgebraic_over_first_output Y hY w hz
  change IsAlgebraic (IntermediateField.adjoin K {r}) v at halg
  have hm := mem_algebraicClosure_iff.mpr halg
  rw [hR, IntermediateField.mem_bot] at hm
  obtain ⟨a, rfl⟩ := hm
  exact a.property

end DimensionFourDependence
