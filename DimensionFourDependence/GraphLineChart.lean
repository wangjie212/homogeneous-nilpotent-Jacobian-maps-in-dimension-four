import DimensionFourDependence.Basic

/-! # Matrix charts for projective lines in dimension four

A two-by-two matrix parametrizes its graph, a two-dimensional subspace.
Two graph lines are skew precisely when their matrix difference has
nonzero determinant. These are actual subspaces in four coordinates.
-/

namespace DimensionFourDependence

open Matrix Module

variable {F : Type*} [Field F]

/-- The product of two two-coordinate spaces in the original four-coordinate order. -/
def fourCoordinateEquiv : ((Fin 2 → F) × (Fin 2 → F)) ≃ₗ[F] (Fin 4 → F) where
  toFun x := ![x.1 0, x.1 1, x.2 0, x.2 1]
  invFun x := (![x 0, x 1], ![x 2, x 3])
  left_inv x := by
    apply Prod.ext <;> ext i <;> fin_cases i <;> rfl
  right_inv x := by ext i; fin_cases i <;> rfl
  map_add' x y := by ext i; fin_cases i <;> rfl
  map_smul' r x := by ext i; fin_cases i <;> rfl

/-- The graph line in product coordinates. -/
def graphLine (B : Matrix (Fin 2) (Fin 2) F) :
    Submodule F ((Fin 2 → F) × (Fin 2 → F)) := B.toLin'.graph

/-- Membership in the matrix graph. -/
theorem mem_graphLine (B : Matrix (Fin 2) (Fin 2) F)
    (x : (Fin 2 → F) × (Fin 2 → F)) : x ∈ graphLine B ↔ x.2 = B *ᵥ x.1 := Iff.rfl

/-- Every matrix graph is a genuine projective line. -/
theorem graphLine_finrank (B : Matrix (Fin 2) (Fin 2) F) :
    finrank F (graphLine B) = 2 := by
  rw [graphLine, LinearMap.graph_eq_range_prod]
  have hinj : Function.Injective (LinearMap.id.prod B.toLin') := by
    intro u v h
    exact congrArg Prod.fst h
  rw [LinearMap.finrank_range_of_inj hinj, Module.finrank_pi, Fintype.card_fin]

/-- A common graph point is equivalent to a vector killed by the matrix difference. -/
theorem graphLine_disjoint_iff_kernel (B C : Matrix (Fin 2) (Fin 2) F) :
    Disjoint (graphLine B) (graphLine C) ↔ ∀ u, (B - C) *ᵥ u = 0 → u = 0 := by
  constructor
  · intro h u hu
    have he : B *ᵥ u = C *ᵥ u := by
      apply sub_eq_zero.mp
      simpa only [sub_mulVec] using hu
    have hz := Submodule.disjoint_def.mp h (u, B *ᵥ u) rfl he
    exact congrArg Prod.fst hz
  · intro h
    apply Submodule.disjoint_def.mpr
    intro x hB hC
    change x.2 = B *ᵥ x.1 at hB
    change x.2 = C *ᵥ x.1 at hC
    have hk : (B - C) *ᵥ x.1 = 0 := by
      rw [sub_mulVec]
      exact sub_eq_zero.mpr (hB.symm.trans hC)
    have hx := h x.1 hk
    apply Prod.ext hx
    change x.2 = 0
    rw [hB, hx, mulVec_zero]

/-- Skewness in a graph chart is a nonvanishing determinant condition. -/
theorem graphLine_disjoint_iff_det (B C : Matrix (Fin 2) (Fin 2) F) :
    Disjoint (graphLine B) (graphLine C) ↔ (B - C).det ≠ 0 := by
  rw [graphLine_disjoint_iff_kernel]
  change (∀ u, (B - C).toLin' u = 0 → u = 0) ↔ _
  rw [← injective_iff_map_eq_zero (B - C).toLin']
  change Function.Injective (B - C).mulVec ↔ _
  rw [Matrix.mulVec_injective_iff_isUnit, Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]

/-- The graph line transported into the original four-coordinate vector space. -/
def graphLineFour (B : Matrix (Fin 2) (Fin 2) F) : Submodule F (Fin 4 → F) :=
  (graphLine B).map (fourCoordinateEquiv (F := F)).toLinearMap

/-- The actual point parametrization of the four-coordinate graph line. -/
theorem mem_graphLineFour (B : Matrix (Fin 2) (Fin 2) F) (x : Fin 4 → F) :
    x ∈ graphLineFour B ↔ ∃ u : Fin 2 → F,
      x = ![u 0, u 1, (B *ᵥ u) 0, (B *ᵥ u) 1] := by
  constructor
  · rintro ⟨p, hp, rfl⟩
    refine ⟨p.1, ?_⟩
    change ![p.1 0, p.1 1, p.2 0, p.2 1] = _
    rw [(mem_graphLine B p).mp hp]
  · rintro ⟨u, rfl⟩
    exact ⟨(u, B *ᵥ u), rfl, rfl⟩

/-- The transported graph still has vector dimension two. -/
theorem graphLineFour_finrank (B : Matrix (Fin 2) (Fin 2) F) :
    finrank F (graphLineFour B) = 2 := by
  rw [graphLineFour, LinearEquiv.finrank_map_eq, graphLine_finrank]

/-- Changing from product to four-coordinate notation preserves skewness. -/
theorem graphLineFour_disjoint_iff (B C : Matrix (Fin 2) (Fin 2) F) :
    Disjoint (graphLineFour B) (graphLineFour C) ↔ Disjoint (graphLine B) (graphLine C) := by
  constructor
  · intro h
    apply Submodule.disjoint_def.mpr
    intro x hB hC
    have hz := Submodule.disjoint_def.mp h (fourCoordinateEquiv x)
      ⟨x, hB, rfl⟩ ⟨x, hC, rfl⟩
    exact (map_eq_zero_iff (fourCoordinateEquiv (F := F)) fourCoordinateEquiv.injective).mp hz
  · intro h
    exact Submodule.disjoint_map fourCoordinateEquiv.injective h

/-- The determinant condition holds for the actual four-coordinate line spans. -/
theorem graphLineFour_disjoint_iff_det (B C : Matrix (Fin 2) (Fin 2) F) :
    Disjoint (graphLineFour B) (graphLineFour C) ↔ (B - C).det ≠ 0 := by
  rw [graphLineFour_disjoint_iff, graphLine_disjoint_iff_det]

end DimensionFourDependence
