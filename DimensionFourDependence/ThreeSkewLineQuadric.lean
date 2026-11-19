import DimensionFourDependence.StandardRulingQuadric

/-! # The quadric and transversals of three skew lines

Transfer of the determinant-quadric transversal theorem to arbitrary
mutually complementary line subspaces. This does not assert the existence
of three skew members of a covering family or the required incidence density.
-/

namespace DimensionFourDependence

variable {F A : Type*} [Field F] [AddCommGroup A] [Module F A]

/-- In axis/axis/diagonal coordinates, every line meeting the original three
subspaces lies on the determinant quadric. -/
theorem coordinate_quadric_contains_transversal
    (U V W : Submodule F A) (e : A ≃ₗ[F] ((Fin 2 → F) × (Fin 2 → F)))
    (hU : ∀ x, (e x).2 = 0 ↔ x ∈ U) (hV : ∀ x, (e x).1 = 0 ↔ x ∈ V)
    (hW : ∀ x, (e x).1 = (e x).2 ↔ x ∈ W)
    (L : Submodule F A) (hL : Module.finrank F L = 2)
    (hLU : ∃ x : A, x ≠ 0 ∧ x ∈ L ∧ x ∈ U)
    (hLV : ∃ x : A, x ≠ 0 ∧ x ∈ L ∧ x ∈ V)
    (hLW : ∃ x : A, x ≠ 0 ∧ x ∈ L ∧ x ∈ W) :
    ∀ x ∈ L, standardRulingQuadric (e x) = 0 := by
  have hdim : Module.finrank F (L.map e.toLinearMap) = 2 := by
    rw [e.finrank_map_eq, hL]
  have hfirst : ∃ a : Fin 2 → F, a ≠ 0 ∧ (a, 0) ∈ L.map e.toLinearMap := by
    obtain ⟨x, hx, hxL, hxU⟩ := hLU
    have hzero := (hU x).mpr hxU
    have he : e x = ((e x).1, 0) := Prod.ext rfl hzero
    refine ⟨(e x).1, ?_, ?_⟩
    · intro hz
      apply hx
      have hex : e x = 0 := by
        change e x = (0, 0)
        simpa only [hz] using he
      exact (map_eq_zero_iff e e.injective).mp hex
    · exact ⟨x, hxL, he⟩
  have hsecond : ∃ b : Fin 2 → F, b ≠ 0 ∧ (0, b) ∈ L.map e.toLinearMap := by
    obtain ⟨x, hx, hxL, hxV⟩ := hLV
    have hzero := (hV x).mpr hxV
    have he : e x = (0, (e x).2) := Prod.ext hzero rfl
    refine ⟨(e x).2, ?_, ?_⟩
    · intro hz
      apply hx
      have hex : e x = 0 := by
        change e x = (0, 0)
        simpa only [hz] using he
      exact (map_eq_zero_iff e e.injective).mp hex
    · exact ⟨x, hxL, he⟩
  have hdiagonal : ∃ c : Fin 2 → F, c ≠ 0 ∧ (c, c) ∈ L.map e.toLinearMap := by
    obtain ⟨x, hx, hxL, hxW⟩ := hLW
    have hdiag := (hW x).mpr hxW
    have he : e x = ((e x).1, (e x).1) := Prod.ext rfl hdiag.symm
    refine ⟨(e x).1, ?_, ?_⟩
    · intro hz
      apply hx
      have hex : e x = 0 := by
        change e x = (0, 0)
        simpa only [hz] using he
      exact (map_eq_zero_iff e e.injective).mp hex
    · exact ⟨x, hxL, he⟩
  intro x hx
  exact line_meeting_three_standard_lines_lies_on_quadric (L.map e.toLinearMap)
    hdim hfirst hsecond hdiagonal (e x) ⟨x, hx, rfl⟩

/-- Three pairwise complementary two-dimensional line subspaces admit a
determinant quadric containing them and all lines meeting all three. -/
theorem three_skew_lines_quadric_transversals [FiniteDimensional F A]
    (U V W : Submodule F A) (hUV : IsCompl U V) (hUW : IsCompl U W)
    (hVW : IsCompl V W) (hW : Module.finrank F W = 2) :
    ∃ e : A ≃ₗ[F] ((Fin 2 → F) × (Fin 2 → F)),
      (∀ x ∈ U, standardRulingQuadric (e x) = 0) ∧
      (∀ x ∈ V, standardRulingQuadric (e x) = 0) ∧
      (∀ x ∈ W, standardRulingQuadric (e x) = 0) ∧
      (∀ (L : Submodule F A), Module.finrank F L = 2 →
        (∃ x : A, x ≠ 0 ∧ x ∈ L ∧ x ∈ U) →
        (∃ x : A, x ≠ 0 ∧ x ∈ L ∧ x ∈ V) →
        (∃ x : A, x ≠ 0 ∧ x ∈ L ∧ x ∈ W) →
        ∀ x ∈ L, standardRulingQuadric (e x) = 0) := by
  obtain ⟨e, heU, heV, heW⟩ :=
    three_skew_lines_coordinate_normal_form U V W hUV hUW hVW hW
  refine ⟨e, ?_, ?_, ?_, coordinate_quadric_contains_transversal U V W e heU heV heW⟩
  · intro x hx
    have he : e x = ((e x).1, 0) := Prod.ext rfl ((heU x).mpr hx)
    rw [he]
    exact (standardRulingQuadric_three_lines _).1
  · intro x hx
    have he : e x = (0, (e x).2) := Prod.ext ((heV x).mpr hx) rfl
    rw [he]
    exact (standardRulingQuadric_three_lines _).2.1
  · intro x hx
    have he : e x = ((e x).1, (e x).1) := Prod.ext rfl ((heW x).mpr hx).symm
    rw [he]
    exact (standardRulingQuadric_three_lines _).2.2

end DimensionFourDependence
