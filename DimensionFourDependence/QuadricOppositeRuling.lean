import DimensionFourDependence.SkewProjectiveLineQuadric

/-! # The opposite ruling of the three standard skew lines

Common transversals are precisely the spans of `(c,0)` and `(0,c)`.
These spans are two-dimensional for `c ≠ 0`, lie on the determinant quadric,
and cover all its nonzero points. No parameter-family dimension assertion
or density of incidence on a general surface is used here.
-/

namespace DimensionFourDependence

variable {F : Type*} [Field F]

/-- A line in the ruling opposite to the three standard skew lines. -/
def standardOppositeRulingLine (c : Fin 2 → F) :
    Submodule F ((Fin 2 → F) × (Fin 2 → F)) :=
  Submodule.span F (Set.range ![(c, (0 : Fin 2 → F)), (0, c)])

/-- The scalar parametrization of an opposite-ruling line. -/
theorem mem_standardOppositeRulingLine_iff (c : Fin 2 → F)
    (x : (Fin 2 → F) × (Fin 2 → F)) :
    x ∈ standardOppositeRulingLine c ↔ ∃ r s : F, x = (r • c, s • c) := by
  constructor
  · intro hx
    obtain ⟨d, hd⟩ := (Submodule.mem_span_range_iff_exists_fun (R := F)).mp hx
    have he : d 0 • (c, (0 : Fin 2 → F)) + d 1 • (0, c) = x := by
      simpa only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons] using hd
    exact ⟨d 0, d 1, by simpa using he.symm⟩
  · rintro ⟨r, s, rfl⟩
    have hfirst : (c, (0 : Fin 2 → F)) ∈ standardOppositeRulingLine c :=
      Submodule.subset_span ⟨0, rfl⟩
    have hsecond : ((0 : Fin 2 → F), c) ∈ standardOppositeRulingLine c :=
      Submodule.subset_span ⟨1, rfl⟩
    simpa using (standardOppositeRulingLine c).add_mem
      ((standardOppositeRulingLine c).smul_mem r hfirst)
      ((standardOppositeRulingLine c).smul_mem s hsecond)

/-- A nonzero parameter gives a genuine projective line. -/
theorem standardOppositeRulingLine_finrank (c : Fin 2 → F) (hc : c ≠ 0) :
    Module.finrank F (standardOppositeRulingLine c) = 2 := by
  exact finrank_span_eq_card (standard_axes_pair_independent c c hc hc)

/-- Every opposite-ruling line is contained in the determinant quadric. -/
theorem standardOppositeRulingLine_quadric (c : Fin 2 → F)
    (x : (Fin 2 → F) × (Fin 2 → F)) (hx : x ∈ standardOppositeRulingLine c) :
    standardRulingQuadric x = 0 := by
  exact standard_axis_span_quadric c c (by ring) x hx

/-- A common transversal of the standard three lines belongs to their opposite ruling. -/
theorem line_meeting_three_standard_lines_opposite_ruling
    (L : Submodule F ((Fin 2 → F) × (Fin 2 → F))) (hL : Module.finrank F L = 2)
    (hfirst : ∃ a : Fin 2 → F, a ≠ 0 ∧ (a, 0) ∈ L)
    (hsecond : ∃ b : Fin 2 → F, b ≠ 0 ∧ (0, b) ∈ L)
    (hdiagonal : ∃ c : Fin 2 → F, c ≠ 0 ∧ (c, c) ∈ L) :
    ∃ c : Fin 2 → F, c ≠ 0 ∧ L = standardOppositeRulingLine c := by
  obtain ⟨a, ha, haL⟩ := hfirst
  obtain ⟨b, hb, hbL⟩ := hsecond
  obtain ⟨c, hc, hcL⟩ := hdiagonal
  have hspan := standard_axes_span L hL a b ha hb haL hbL
  obtain ⟨d, hd⟩ := (Submodule.mem_span_range_iff_exists_fun (R := F)).mp (hspan ▸ hcL)
  have he : d 0 • (a, (0 : Fin 2 → F)) + d 1 • (0, b) = (c, c) := by
    simpa only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons] using hd
  have heA : d 0 • a = c := by simpa using congrArg Prod.fst he
  have heB : d 1 • b = c := by simpa using congrArg Prod.snd he
  have hcfirst : (c, (0 : Fin 2 → F)) ∈ L := by
    have hm := L.smul_mem (d 0) haL
    simpa only [Prod.smul_mk, smul_zero, heA] using hm
  have hcsecond : ((0 : Fin 2 → F), c) ∈ L := by
    have hm := L.smul_mem (d 1) hbL
    simpa only [Prod.smul_mk, smul_zero, heB] using hm
  exact ⟨c, hc, (standard_axes_span L hL c c hc hc hcfirst hcsecond).symm⟩

/-- In two coordinates, a zero determinant with a nonzero first vector
is equivalent to proportionality (the needed direction). -/
theorem determinant_zero_exists_smul (a b : Fin 2 → F) (ha : a ≠ 0)
    (hdet : a 0 * b 1 - a 1 * b 0 = 0) : ∃ s : F, b = s • a := by
  by_cases ha0 : a 0 = 0
  · have ha1 : a 1 ≠ 0 := by
      intro hz
      apply ha
      ext i
      fin_cases i <;> assumption
    have hb0 : b 0 = 0 := by
      have hz : a 1 * b 0 = 0 := by simpa [ha0] using hdet
      exact (mul_eq_zero.mp hz).resolve_left ha1
    refine ⟨b 1 / a 1, ?_⟩
    ext i
    fin_cases i
    · simp [ha0, hb0]
    · change b 1 = b 1 / a 1 * a 1
      field_simp
  · refine ⟨b 0 / a 0, ?_⟩
    ext i
    fin_cases i
    · change b 0 = b 0 / a 0 * a 0
      field_simp
    · change b 1 = b 0 / a 0 * a 1
      apply mul_left_cancel₀ ha0
      calc
        a 0 * b 1 = a 1 * b 0 := sub_eq_zero.mp hdet
        _ = a 0 * (b 0 / a 0 * a 1) := by field_simp

/-- The opposite-ruling lines cover every projective point of the determinant quadric. -/
theorem standard_quadric_point_on_opposite_ruling
    (x : (Fin 2 → F) × (Fin 2 → F)) (hx : x ≠ 0) (hq : standardRulingQuadric x = 0) :
    ∃ c : Fin 2 → F, c ≠ 0 ∧ x ∈ standardOppositeRulingLine c := by
  by_cases hfirst : x.1 = 0
  · have hsecond : x.2 ≠ 0 := by
      intro hz
      exact hx (Prod.ext hfirst hz)
    refine ⟨x.2, hsecond, (mem_standardOppositeRulingLine_iff _ _).mpr ?_⟩
    refine ⟨0, 1, ?_⟩
    apply Prod.ext
    · simpa using hfirst
    · simp
  · obtain ⟨s, hs⟩ := determinant_zero_exists_smul x.1 x.2 hfirst hq
    refine ⟨x.1, hfirst, (mem_standardOppositeRulingLine_iff _ _).mpr ?_⟩
    refine ⟨1, s, ?_⟩
    apply Prod.ext
    · simp
    · exact hs

end DimensionFourDependence
