import DimensionFourDependence.Basic

/-! # The slope charts for all plane lines through a fixed projective point

At `[1:0:0]`, every projective line is the span of `(1,0,0)` and
`(0,1,m)` for one slope, or the exceptional span of `(1,0,0),(0,0,1)`.
All statements concern actual two-dimensional vector subspaces.
-/

namespace DimensionFourDependence

open Module

variable {F : Type*} [Field F]

/-- The line of finite slope through the first coordinate point. -/
def standardPlaneLine (m : F) : Submodule F (Fin 3 → F) :=
  Submodule.span F (Set.range ![(![1, 0, 0] : Fin 3 → F), ![0, 1, m]])

/-- The exceptional line in the slope chart. -/
def standardVerticalPlaneLine : Submodule F (Fin 3 → F) :=
  Submodule.span F (Set.range ![(![1, 0, 0] : Fin 3 → F), ![0, 0, 1]])

/-- The finite-slope generators are independent. -/
theorem standardPlaneLine_generators_independent (m : F) :
    LinearIndependent F ![(![1, 0, 0] : Fin 3 → F), ![0, 1, m]] := by
  rw [LinearIndependent.pair_iff]
  intro r s he
  have h0 := congrFun he 0
  have h1 := congrFun he 1
  exact ⟨by simpa using h0, by simpa using h1⟩

/-- Each finite-slope span is a genuine projective line. -/
theorem standardPlaneLine_finrank (m : F) : finrank F (standardPlaneLine m) = 2 :=
  finrank_span_eq_card (standardPlaneLine_generators_independent m)

/-- The exceptional span is also a genuine projective line. -/
theorem standardVerticalPlaneLine_finrank : finrank F (standardVerticalPlaneLine (F := F)) = 2 := by
  apply finrank_span_eq_card
  rw [LinearIndependent.pair_iff]
  intro r s he
  have h0 := congrFun he 0
  have h2 := congrFun he 2
  exact ⟨by simpa using h0, by simpa using h2⟩

/-- A useful normalized point on the line of a given slope. -/
theorem standardPlaneLine_normalized_point_mem (m s : F) :
    (![s, 1, m] : Fin 3 → F) ∈ standardPlaneLine m := by
  have h0 : (![1, 0, 0] : Fin 3 → F) ∈ standardPlaneLine m := Submodule.subset_span ⟨0, rfl⟩
  have h1 : (![0, 1, m] : Fin 3 → F) ∈ standardPlaneLine m := Submodule.subset_span ⟨1, rfl⟩
  have hm := (standardPlaneLine m).add_mem ((standardPlaneLine m).smul_mem s h0) h1
  have he : s • (![1, 0, 0] : Fin 3 → F) + ![0, 1, m] = ![s, 1, m] := by
    ext i
    fin_cases i <;> simp
  exact he ▸ hm

/-- A vector with zero second coordinate belongs to the exceptional line. -/
theorem standardVerticalPlaneLine_mem_of_second_zero (x : Fin 3 → F) (hx : x 1 = 0) :
    x ∈ standardVerticalPlaneLine := by
  have h0 : (![1, 0, 0] : Fin 3 → F) ∈ standardVerticalPlaneLine := Submodule.subset_span ⟨0, rfl⟩
  have h2 : (![0, 0, 1] : Fin 3 → F) ∈ standardVerticalPlaneLine := Submodule.subset_span ⟨1, rfl⟩
  have hm := standardVerticalPlaneLine.add_mem
    (standardVerticalPlaneLine.smul_mem (x 0) h0) (standardVerticalPlaneLine.smul_mem (x 2) h2)
  have he : x 0 • (![1, 0, 0] : Fin 3 → F) + x 2 • ![0, 0, 1] = x := by
    ext i
    fin_cases i <;> simp [hx]
  exact he ▸ hm

/-- The slope chart and its one exceptional line cover all projective
lines in the plane through the first coordinate point. -/
theorem plane_line_through_first_point_classification
    (L : Submodule F (Fin 3 → F)) (hL : finrank F L = 2)
    (hO : (![1, 0, 0] : Fin 3 → F) ∈ L) :
    L = standardVerticalPlaneLine ∨ ∃ m : F, L = standardPlaneLine m := by
  classical
  by_cases hpoint : ∃ v ∈ L, v 1 ≠ 0
  · obtain ⟨v, hv, hv1⟩ := hpoint
    let D := (v 1)⁻¹ • (v - v 0 • (![1, 0, 0] : Fin 3 → F))
    have hD : D ∈ L := L.smul_mem _ (L.sub_mem hv (L.smul_mem _ hO))
    have he : D = (![0, 1, v 2 / v 1] : Fin 3 → F) := by
      ext i
      fin_cases i
      · change (v 1)⁻¹ * (v 0 - v 0 * 1) = 0
        ring
      · change (v 1)⁻¹ * (v 1 - v 0 * 0) = 1
        simp [hv1]
      · change (v 1)⁻¹ * (v 2 - v 0 * 0) = v 2 / v 1
        rw [div_eq_mul_inv]
        ring
    rw [he] at hD
    have hle : standardPlaneLine (v 2 / v 1) ≤ L := by
      apply Submodule.span_le.mpr
      rintro _ ⟨i, rfl⟩
      fin_cases i
      · exact hO
      · exact hD
    exact Or.inr ⟨v 2 / v 1, (Submodule.eq_of_le_of_finrank_eq hle
      ((standardPlaneLine_finrank _).trans hL.symm)).symm⟩
  · left
    have hle : L ≤ standardVerticalPlaneLine := by
      intro x hx
      apply standardVerticalPlaneLine_mem_of_second_zero
      by_contra hne
      exact hpoint ⟨x, hx, hne⟩
    exact Submodule.eq_of_le_of_finrank_eq hle (hL.trans standardVerticalPlaneLine_finrank.symm)

end DimensionFourDependence
