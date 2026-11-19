import DimensionFourDependence.ThreeSkewLineCoordinates

/-! # Lines meeting the three standard skew lines

The axes and diagonal in a product of two two-dimensional vector spaces
lie on the determinant quadric. Every projective line meeting all three
lies entirely on that quadric. This proves the elementary transversal
step, separately from the surface-family incidence argument.
-/

namespace DimensionFourDependence

variable {F : Type*} [Field F]

/-- The determinant quadric in product coordinates. -/
def standardRulingQuadric (x : (Fin 2 → F) × (Fin 2 → F)) : F :=
  x.1 0 * x.2 1 - x.1 1 * x.2 0

/-- The two axes and diagonal are contained in the determinant quadric. -/
theorem standardRulingQuadric_three_lines (a : Fin 2 → F) :
    standardRulingQuadric (a, 0) = 0 ∧
      standardRulingQuadric (0, a) = 0 ∧ standardRulingQuadric (a, a) = 0 := by
  simp [standardRulingQuadric, mul_comm]

/-- Nonzero vectors on the two different axes are independent. -/
theorem standard_axes_pair_independent (a b : Fin 2 → F) (ha : a ≠ 0) (hb : b ≠ 0) :
    LinearIndependent F ![(a, (0 : Fin 2 → F)), (0, b)] := by
  rw [Fintype.linearIndependent_iff]
  intro c hc
  have he : c 0 • (a, (0 : Fin 2 → F)) + c 1 • (0, b) = 0 := by
    simpa only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons] using hc
  have hca : c 0 • a = 0 := by
    simpa using congrArg Prod.fst he
  have hcb : c 1 • b = 0 := by
    simpa using congrArg Prod.snd he
  intro i
  fin_cases i
  · exact (smul_eq_zero.mp hca).resolve_right ha
  · exact (smul_eq_zero.mp hcb).resolve_right hb

/-- A two-dimensional subspace meeting both axes is spanned by its axis intersections. -/
theorem standard_axes_span (L : Submodule F ((Fin 2 → F) × (Fin 2 → F)))
    (hL : Module.finrank F L = 2) (a b : Fin 2 → F) (ha : a ≠ 0) (hb : b ≠ 0)
    (haL : (a, 0) ∈ L) (hbL : (0, b) ∈ L) :
    Submodule.span F (Set.range ![(a, (0 : Fin 2 → F)), (0, b)]) = L := by
  apply Submodule.eq_of_le_of_finrank_eq
  · apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    fin_cases i
    · exact haL
    · exact hbL
  · rw [finrank_span_eq_card (standard_axes_pair_independent a b ha hb), hL]
    rfl

/-- A common nonzero diagonal point forces the two axis coordinates to be proportional. -/
theorem standard_transversal_axis_determinant (a b c : Fin 2 → F) (hc : c ≠ 0)
    (hmem : (c, c) ∈ Submodule.span F (Set.range ![(a, (0 : Fin 2 → F)), (0, b)])) :
    a 0 * b 1 - a 1 * b 0 = 0 := by
  obtain ⟨d, hd⟩ := (Submodule.mem_span_range_iff_exists_fun (R := F)).mp hmem
  have he : d 0 • (a, (0 : Fin 2 → F)) + d 1 • (0, b) = (c, c) := by
    simpa only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons] using hd
  have heA : d 0 • a = c := by simpa using congrArg Prod.fst he
  have heB : d 1 • b = c := by simpa using congrArg Prod.snd he
  have hd0 : d 0 ≠ 0 := by
    intro hz
    exact hc (by simpa [hz] using heA.symm)
  have he0 : d 0 * a 0 = d 1 * b 0 := by
    simpa using congrFun (heA.trans heB.symm) 0
  have he1 : d 0 * a 1 = d 1 * b 1 := by
    simpa using congrFun (heA.trans heB.symm) 1
  have hz : d 0 * (a 0 * b 1 - a 1 * b 0) = 0 := by
    calc
      _ = (d 0 * a 0) * b 1 - (d 0 * a 1) * b 0 := by ring
      _ = (d 1 * b 0) * b 1 - (d 1 * b 1) * b 0 := by rw [he0, he1]
      _ = 0 := by ring
  exact (mul_eq_zero.mp hz).resolve_left hd0

/-- The span of two proportional axis coordinates lies on the determinant quadric. -/
theorem standard_axis_span_quadric (a b : Fin 2 → F)
    (hab : a 0 * b 1 - a 1 * b 0 = 0)
    (x : (Fin 2 → F) × (Fin 2 → F))
    (hx : x ∈ Submodule.span F (Set.range ![(a, (0 : Fin 2 → F)), (0, b)])) :
    standardRulingQuadric x = 0 := by
  obtain ⟨d, hd⟩ := (Submodule.mem_span_range_iff_exists_fun (R := F)).mp hx
  have he : d 0 • (a, (0 : Fin 2 → F)) + d 1 • (0, b) = x := by
    simpa only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons] using hd
  rw [← he]
  change (d 0 * a 0 + d 1 * 0) * (d 0 * 0 + d 1 * b 1) -
    (d 0 * a 1 + d 1 * 0) * (d 0 * 0 + d 1 * b 0) = 0
  calc
    _ = d 0 * d 1 * (a 0 * b 1 - a 1 * b 0) := by ring
    _ = 0 := by rw [hab, mul_zero]

/-- Any projective line meeting all three standard skew lines lies on their quadric. -/
theorem line_meeting_three_standard_lines_lies_on_quadric
    (L : Submodule F ((Fin 2 → F) × (Fin 2 → F))) (hL : Module.finrank F L = 2)
    (hfirst : ∃ a : Fin 2 → F, a ≠ 0 ∧ (a, 0) ∈ L)
    (hsecond : ∃ b : Fin 2 → F, b ≠ 0 ∧ (0, b) ∈ L)
    (hdiagonal : ∃ c : Fin 2 → F, c ≠ 0 ∧ (c, c) ∈ L) :
    ∀ x ∈ L, standardRulingQuadric x = 0 := by
  obtain ⟨a, ha, haL⟩ := hfirst
  obtain ⟨b, hb, hbL⟩ := hsecond
  obtain ⟨c, hc, hcL⟩ := hdiagonal
  have hspan := standard_axes_span L hL a b ha hb haL hbL
  have hdet := standard_transversal_axis_determinant a b c hc (hspan ▸ hcL)
  intro x hx
  exact standard_axis_span_quadric a b hdet x (hspan ▸ hx)

end DimensionFourDependence
