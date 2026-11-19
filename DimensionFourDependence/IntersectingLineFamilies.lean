import DimensionFourDependence.IntersectingLineGeometry

/-! # Pairwise-intersecting families of projective lines

The plane-or-concurrent alternative is proved for arbitrary families of
two-dimensional subspaces. No algebraic parameter-space or incidence-density
assumption is required for this elementary part of the Section 3.2 argument.
-/

namespace DimensionFourDependence

variable {F A : Type*} [Field F] [AddCommGroup A] [Module F A] [FiniteDimensional F A]

/-- A pairwise-intersecting line family either lies in a projective plane
or all its lines pass through one projective point. The plane is allowed
smaller vector dimension to include the empty and single-line cases. -/
theorem intersecting_line_family_plane_or_point
    (S : Set (Submodule F A)) (hdim : ∀ L ∈ S, Module.finrank F L = 2)
    (hmeet : ∀ U ∈ S, ∀ V ∈ S, U ⊓ V ≠ ⊥) :
    (∃ P : Submodule F A, Module.finrank F P ≤ 3 ∧ ∀ L ∈ S, L ≤ P) ∨
      (∃ T : Submodule F A, Module.finrank F T = 1 ∧ ∀ L ∈ S, T ≤ L) := by
  classical
  by_cases hpair : ∃ U ∈ S, ∃ V ∈ S, U ≠ V
  · obtain ⟨U, hUS, V, hVS, hne⟩ := hpair
    have hU := hdim U hUS
    have hV := hdim V hVS
    have hUV := hmeet U hUS V hVS
    have hd := distinct_intersecting_lines_dimensions U V hU hV hne hUV
    by_cases hplane : ∀ L ∈ S, L ≤ U ⊔ V
    · exact Or.inl ⟨U ⊔ V, by omega, hplane⟩
    · push Not at hplane
      obtain ⟨W, hWS, hWP⟩ := hplane
      have hTW : U ⊓ V ≤ W :=
        (line_meeting_intersecting_pair U V W hU hV (hdim W hWS) hne hUV
          (hmeet W hWS U hUS) (hmeet W hWS V hVS)).resolve_left hWP
      refine Or.inr ⟨U ⊓ V, hd.1, ?_⟩
      intro L hLS
      by_cases hLP : L ≤ U ⊔ V
      · exact inside_line_meeting_outside_contains_point W (U ⊔ V) (U ⊓ V) L
          (hdim W hWS) hd.1 hWP hTW (le_trans inf_le_left le_sup_left)
          hLP (hmeet W hWS L hLS)
      · exact (line_meeting_intersecting_pair U V L hU hV (hdim L hLS) hne hUV
          (hmeet L hLS U hUS) (hmeet L hLS V hVS)).resolve_left hLP
  · left
    by_cases hnonempty : S.Nonempty
    · obtain ⟨U, hUS⟩ := hnonempty
      refine ⟨U, by rw [hdim U hUS]; omega, ?_⟩
      intro L hLS
      have he : L = U := by
        by_contra hne
        exact hpair ⟨L, hLS, U, hUS, hne⟩
      exact he.le
    · exact ⟨⊥, by simp, fun L hLS => False.elim (hnonempty ⟨L, hLS⟩)⟩

/-- The usual pairwise-intersection formulation of the plane-or-point alternative. -/
theorem pairwise_intersecting_projective_lines_plane_or_point
    (S : Set (Submodule F A)) (hdim : ∀ L ∈ S, Module.finrank F L = 2)
    (hpair : S.Pairwise (fun U V => ¬ Disjoint U V)) :
    (∃ P : Submodule F A, Module.finrank F P ≤ 3 ∧ ∀ L ∈ S, L ≤ P) ∨
      (∃ T : Submodule F A, Module.finrank F T = 1 ∧ ∀ L ∈ S, T ≤ L) := by
  apply intersecting_line_family_plane_or_point S hdim
  intro U hUS V hVS
  by_cases he : U = V
  · subst V
    rw [inf_idem]
    intro hzero
    have hd := hdim U hUS
    rw [hzero] at hd
    simp at hd
  · intro hzero
    exact hpair hUS hVS he (disjoint_iff_inf_le.mpr hzero.le)

/-- A family which is neither coplanar nor concurrent has two skew members.
Producing three general skew members additionally uses parameter-space geometry. -/
theorem noncoplanar_nonconcurrent_line_family_has_skew_pair
    (S : Set (Submodule F A)) (hdim : ∀ L ∈ S, Module.finrank F L = 2)
    (hnotplane : ¬ ∃ P : Submodule F A, Module.finrank F P ≤ 3 ∧ ∀ L ∈ S, L ≤ P)
    (hnotpoint : ¬ ∃ T : Submodule F A, Module.finrank F T = 1 ∧ ∀ L ∈ S, T ≤ L) :
    ∃ U ∈ S, ∃ V ∈ S, Disjoint U V := by
  classical
  by_contra hnone
  have hpair : S.Pairwise (fun U V => ¬ Disjoint U V) := by
    intro U hUS V hVS _ hdisjoint
    exact hnone ⟨U, hUS, V, hVS, hdisjoint⟩
  exact (pairwise_intersecting_projective_lines_plane_or_point S hdim hpair).elim
    hnotplane hnotpoint

end DimensionFourDependence
