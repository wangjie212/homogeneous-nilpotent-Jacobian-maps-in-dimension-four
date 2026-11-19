import DimensionFourDependence.IntersectingLineFamilies

/-! # Selecting three skew members of an irreducible line family

An open symmetric relation with one related pair has related triples in
every nonempty open subset of an irreducible parameter space. Applied to
skewness, the plane-or-concurrent alternative supplies the first pair.
The algebraic parameter space and openness of its skewness relation must
still be constructed for the actual image surface.
-/

namespace DimensionFourDependence

variable {X : Type*} [TopologicalSpace X] [PreirreducibleSpace X]

/-- An open symmetric relation with a related pair has a related triangle
inside every prescribed nonempty open set of a preirreducible space. -/
theorem symmetric_open_relation_triangle_in_open
    (R : X → X → Prop) (hsymm : ∀ ⦃a b⦄, R a b → R b a)
    (hopen : ∀ a, IsOpen {b : X | R a b}) (hpair : ∃ a b, R a b)
    (O : Set X) (hO : IsOpen O) (hOne : O.Nonempty) :
    ∃ a ∈ O, ∃ b ∈ O, ∃ c ∈ O, R a b ∧ R a c ∧ R b c := by
  obtain ⟨u, v, huv⟩ := hpair
  obtain ⟨a, haO, hva⟩ := nonempty_preirreducible_inter hO (hopen v)
    hOne ⟨u, hsymm huv⟩
  obtain ⟨b, hbO, hab⟩ := nonempty_preirreducible_inter hO (hopen a)
    hOne ⟨v, hsymm hva⟩
  have hboth : ({c : X | R a c} ∩ {c : X | R b c}).Nonempty :=
    nonempty_preirreducible_inter (hopen a) (hopen b) ⟨b, hab⟩ ⟨a, hsymm hab⟩
  obtain ⟨c, hcO, hac, hbc⟩ := nonempty_preirreducible_inter hO
    ((hopen a).inter (hopen b)) hOne hboth
  exact ⟨a, haO, b, hbO, c, hcO, hab, hac, hbc⟩

variable {F A : Type*} [Field F] [AddCommGroup A] [Module F A]

/-- If skewness is open in an irreducible family, a single skew pair gives
three pairwise skew members in every nonempty open part of that family. -/
theorem irreducible_line_family_skew_triple_in_open
    (L : X → Submodule F A) (hopen : ∀ a, IsOpen {b : X | Disjoint (L a) (L b)})
    (hpair : ∃ a b, Disjoint (L a) (L b))
    (O : Set X) (hO : IsOpen O) (hOne : O.Nonempty) :
    ∃ a ∈ O, ∃ b ∈ O, ∃ c ∈ O,
      Disjoint (L a) (L b) ∧ Disjoint (L a) (L c) ∧ Disjoint (L b) (L c) := by
  exact symmetric_open_relation_triangle_in_open (fun a b => Disjoint (L a) (L b))
    (fun _ _ h => h.symm) hopen hpair O hO hOne

/-- A noncoplanar, nonconcurrent irreducible line family with open skewness
has three pairwise skew members on every nonempty open parameter chart. -/
theorem noncoplanar_nonconcurrent_irreducible_family_skew_triple [FiniteDimensional F A]
    (L : X → Submodule F A) (hdim : ∀ a, Module.finrank F (L a) = 2)
    (hopen : ∀ a, IsOpen {b : X | Disjoint (L a) (L b)})
    (hnotplane : ¬ ∃ P : Submodule F A,
      Module.finrank F P ≤ 3 ∧ ∀ a, L a ≤ P)
    (hnotpoint : ¬ ∃ T : Submodule F A,
      Module.finrank F T = 1 ∧ ∀ a, T ≤ L a)
    (O : Set X) (hO : IsOpen O) (hOne : O.Nonempty) :
    ∃ a ∈ O, ∃ b ∈ O, ∃ c ∈ O,
      Disjoint (L a) (L b) ∧ Disjoint (L a) (L c) ∧ Disjoint (L b) (L c) := by
  have hdimrange : ∀ V ∈ Set.range L, Module.finrank F V = 2 := by
    rintro _ ⟨a, rfl⟩
    exact hdim a
  have hplane : ¬ ∃ P : Submodule F A,
      Module.finrank F P ≤ 3 ∧ ∀ V ∈ Set.range L, V ≤ P := by
    rintro ⟨P, hP, hcontain⟩
    exact hnotplane ⟨P, hP, fun a => hcontain (L a) ⟨a, rfl⟩⟩
  have hpoint : ¬ ∃ T : Submodule F A,
      Module.finrank F T = 1 ∧ ∀ V ∈ Set.range L, T ≤ V := by
    rintro ⟨T, hT, hcontain⟩
    exact hnotpoint ⟨T, hT, fun a => hcontain (L a) ⟨a, rfl⟩⟩
  obtain ⟨U, ⟨a, rfl⟩, V, ⟨b, rfl⟩, hab⟩ :=
    noncoplanar_nonconcurrent_line_family_has_skew_pair (Set.range L) hdimrange hplane hpoint
  exact irreducible_line_family_skew_triple_in_open L hopen ⟨a, b, hab⟩ O hO hOne

end DimensionFourDependence
