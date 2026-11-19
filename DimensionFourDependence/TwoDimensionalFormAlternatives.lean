import DimensionFourDependence.RulingFormRelations

/-! # The three binary-form alternatives on an actual two-dimensional ruling

Two independent forms are a basis of the ruling dual. Every third form
therefore has a binary expression. If the first pair is dependent, its
nonzero second member spans the first. These give exactly the three
alternatives preceding the divisor exclusion in Section 4.2.
-/

namespace DimensionFourDependence

open Matrix Module

variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V] [FiniteDimensional F V]

/-- Two independent vectors in a two-dimensional space supply
the actual scalar coefficients of every third vector. -/
theorem two_dimensional_independent_pair_binary_span
    (hdim : finrank F V = 2) (m n s : V) (hpair : LinearIndependent F ![m, n]) :
    ∃ α β : F, s = α • m + β • n := by
  have hcard : Fintype.card (Fin 2) = finrank F V := by rw [hdim]; rfl
  let B := basisOfLinearIndependentOfCardEqFinrank hpair hcard
  have hB0 : B 0 = m := congrFun (coe_basisOfLinearIndependentOfCardEqFinrank hpair hcard) 0
  have hB1 : B 1 = n := congrFun (coe_basisOfLinearIndependentOfCardEqFinrank hpair hcard) 1
  refine ⟨B.repr s 0, B.repr s 1, ?_⟩
  simpa only [Fin.sum_univ_two, hB0, hB1] using (B.sum_repr s).symm

/-- The forms on a two-dimensional ruling satisfy one of the
paper's two proportional cases or its independent binary case with a
nonzero first coefficient. No binary-form relation is assumed. -/
theorem two_dimensional_form_three_alternatives
    (hdim : finrank F V = 2) (m n s : V) (hn : n ≠ 0) :
    (∃ γ : F, m = γ • n) ∨
      (LinearIndependent F ![m, n] ∧ ∃ β : F, s = β • n) ∨
      (LinearIndependent F ![m, n] ∧ ∃ α β : F, α ≠ 0 ∧ s = α • m + β • n) := by
  by_cases hpair : LinearIndependent F ![m, n]
  · obtain ⟨α, β, hlinear⟩ := two_dimensional_independent_pair_binary_span hdim m n s hpair
    by_cases hα : α = 0
    · exact Or.inr (Or.inl ⟨hpair, β, by simpa only [hα, zero_smul, zero_add] using hlinear⟩)
    · exact Or.inr (Or.inr ⟨hpair, α, β, hα, hlinear⟩)
  · have hswap : ¬ LinearIndependent F ![n, m] :=
      fun hnm => hpair (LinearIndependent.pair_symm_iff.mpr hnm)
    rw [LinearIndependent.pair_iff' hn] at hswap
    push Not at hswap
    obtain ⟨γ, hγ⟩ := hswap
    exact Or.inl ⟨γ, hγ.symm⟩

end DimensionFourDependence
