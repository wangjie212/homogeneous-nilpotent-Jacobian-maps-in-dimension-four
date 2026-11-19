import DimensionFourDependence.FullSourceComponents

/-! # Recovering algebraic coefficients inside an algebraically closed base

An embedding of a source field into a geometric component sends its
algebraic coefficient field into the algebraically closed constants.
The coefficient embedding is constructed from these actual images.
-/

namespace DimensionFourDependence

variable {M L F E G : Type*} [Field M] [Field L] [Field F] [Field E] [Field G]
    [Algebra M L] [Algebra L F] [Algebra M F] [IsScalarTower M L F]
    [Algebra M E] [Algebra E G] [Algebra M G] [IsScalarTower M E G]
    [Algebra.IsAlgebraic M L] [IsAlgClosed E]

/-- Every source-field embedding induces the corresponding embedding
of its algebraic coefficient field into the geometric constants. -/
theorem exists_algebraic_coefficient_embedding (f : F →ₐ[M] G) :
    ∃ g : L →ₐ[M] E, ∀ l : L, algebraMap E G (g l) = f (algebraMap L F l) := by
  classical
  have hvalue (l : L) : ∃ e : E, algebraMap E G e = f (algebraMap L F l) := by
    have hm : IsAlgebraic M (algebraMap L F l) :=
      (Algebra.IsAlgebraic.isAlgebraic l).algebraMap
    have he : IsAlgebraic E (f (algebraMap L F l)) := (IsAlgebraic.algHom f hm).tower_top E
    have hmem := mem_algebraicClosure_iff.mpr he
    have hbot : algebraicClosure E G = ⊥ :=
      IntermediateField.eq_bot_of_isAlgClosed_of_isAlgebraic _
    rw [hbot] at hmem
    exact hmem
  let g : L → E := fun l => Classical.choose (hvalue l)
  have hg (l : L) : algebraMap E G (g l) = f (algebraMap L F l) := Classical.choose_spec (hvalue l)
  exact ⟨{
    toFun := g
    map_zero' := by
      apply (algebraMap E G).injective
      simp only [hg, map_zero]
    map_one' := by
      apply (algebraMap E G).injective
      simp only [hg, map_one]
    map_add' := by
      intro a b
      apply (algebraMap E G).injective
      simp only [hg, map_add]
    map_mul' := by
      intro a b
      apply (algebraMap E G).injective
      simp only [hg, map_mul]
    commutes' := by
      intro r
      apply (algebraMap E G).injective
      rw [hg, ← IsScalarTower.algebraMap_apply M L F,
        ← IsScalarTower.algebraMap_apply M E G, f.commutes]
  }, hg⟩

end DimensionFourDependence
