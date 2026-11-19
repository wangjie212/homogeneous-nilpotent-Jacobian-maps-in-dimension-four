import DimensionFourDependence.Basic

/-! # Intersecting projective lines: the elementary subspace geometry

Projective points and lines are represented by one- and two-dimensional
vector subspaces. These lemmas prove the plane-or-common-point alternative
used in the line-family argument in Section 3.2.
-/

namespace DimensionFourDependence

variable {F A : Type*} [Field F] [AddCommGroup A] [Module F A] [FiniteDimensional F A]

/-- A nonzero subspace has positive vector-space dimension. -/
theorem submodule_finrank_positive (S : Submodule F A) (hS : S ≠ ⊥) :
    0 < Module.finrank F S := by
  by_contra h
  exact hS (Submodule.finrank_eq_zero.mp (by omega))

/-- A nonzero subspace of a one-dimensional space is the entire space. -/
theorem submodule_eq_of_le_line (S T : Submodule F A)
    (hT : Module.finrank F T = 1) (hS : S ≠ ⊥) (hle : S ≤ T) : S = T := by
  apply Submodule.eq_of_le_of_finrank_le hle
  have hp := submodule_finrank_positive S hS
  omega

/-- A projective line not contained in a given subspace meets it in at most a point. -/
theorem line_intersection_finrank_le_one (L P : Submodule F A)
    (hL : Module.finrank F L = 2) (hnot : ¬ L ≤ P) :
    Module.finrank F (L ⊓ P : Submodule F A) ≤ 1 := by
  have hlt : L ⊓ P < L := lt_of_le_of_ne inf_le_left (by
    intro he
    apply hnot
    rw [← he]
    exact inf_le_right)
  have hd := Submodule.finrank_lt_finrank_of_lt hlt
  omega

/-- Two distinct intersecting projective lines meet at one point and span a plane. -/
theorem distinct_intersecting_lines_dimensions (U V : Submodule F A)
    (hU : Module.finrank F U = 2) (hV : Module.finrank F V = 2)
    (hne : U ≠ V) (hmeet : U ⊓ V ≠ ⊥) :
    Module.finrank F (U ⊓ V : Submodule F A) = 1 ∧
      Module.finrank F (U ⊔ V : Submodule F A) = 3 := by
  have hnot : ¬ U ≤ V := by
    intro hle
    exact hne (Submodule.eq_of_le_of_finrank_eq hle (hU.trans hV.symm))
  have hupper := line_intersection_finrank_le_one U V hU hnot
  have hpos := submodule_finrank_positive (U ⊓ V) hmeet
  have hinf : Module.finrank F (U ⊓ V : Submodule F A) = 1 := by omega
  have hsum := Submodule.finrank_sup_add_finrank_inf_eq U V
  exact ⟨hinf, by omega⟩

/-- A line meeting two intersecting lines lies in their plane or passes through
their intersection point. -/
theorem line_meeting_intersecting_pair (U V L : Submodule F A)
    (hU : Module.finrank F U = 2) (hV : Module.finrank F V = 2)
    (hL : Module.finrank F L = 2) (hne : U ≠ V) (hUV : U ⊓ V ≠ ⊥)
    (hLU : L ⊓ U ≠ ⊥) (hLV : L ⊓ V ≠ ⊥) :
    L ≤ U ⊔ V ∨ U ⊓ V ≤ L := by
  by_cases hplane : L ≤ U ⊔ V
  · exact Or.inl hplane
  · right
    let P := U ⊔ V
    have hpoint := (distinct_intersecting_lines_dimensions U V hU hV hne hUV).1
    have hupper := line_intersection_finrank_le_one L P hL hplane
    have hpos := submodule_finrank_positive (L ⊓ U) hLU
    have hle : L ⊓ U ≤ L ⊓ P := inf_le_inf_left L le_sup_left
    have hdimle := Submodule.finrank_strictMono.monotone hle
    have hdim : Module.finrank F (L ⊓ P : Submodule F A) = 1 := by omega
    have hleft : L ⊓ U = L ⊓ P := submodule_eq_of_le_line _ _ hdim hLU hle
    have hright : L ⊓ V = L ⊓ P :=
      submodule_eq_of_le_line _ _ hdim hLV (inf_le_inf_left L le_sup_right)
    have hnonzero : L ⊓ P ≠ ⊥ := by
      rw [← hleft]
      exact hLU
    have hboth : L ⊓ P ≤ U ⊓ V := le_inf
      (by rw [← hleft]; exact inf_le_right)
      (by rw [← hright]; exact inf_le_right)
    have he := submodule_eq_of_le_line (L ⊓ P) (U ⊓ V) hpoint hnonzero hboth
    rw [← he]
    exact inf_le_left

/-- A line outside a plane through a given point meets that plane at exactly that point. -/
theorem outside_line_intersection_eq_point (W P T : Submodule F A)
    (hW : Module.finrank F W = 2) (hT : Module.finrank F T = 1)
    (hWP : ¬ W ≤ P) (hTW : T ≤ W) (hTP : T ≤ P) : W ⊓ P = T := by
  have hupper := line_intersection_finrank_le_one W P hW hWP
  exact (Submodule.eq_of_le_of_finrank_le (le_inf hTW hTP) (by omega)).symm

/-- A line inside a plane that meets an outside line through the distinguished
point must also pass through that point. -/
theorem inside_line_meeting_outside_contains_point (W P T L : Submodule F A)
    (hW : Module.finrank F W = 2) (hT : Module.finrank F T = 1)
    (hWP : ¬ W ≤ P) (hTW : T ≤ W) (hTP : T ≤ P)
    (hLP : L ≤ P) (hmeet : W ⊓ L ≠ ⊥) : T ≤ L := by
  have he := outside_line_intersection_eq_point W P T hW hT hWP hTW hTP
  have hle : W ⊓ L ≤ T := by
    rw [← he]
    exact inf_le_inf_left W hLP
  have hpoint := submodule_eq_of_le_line (W ⊓ L) T hT hmeet hle
  rw [← hpoint]
  exact inf_le_right

end DimensionFourDependence
