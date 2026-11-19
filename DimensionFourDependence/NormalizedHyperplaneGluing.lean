import DimensionFourDependence.NormalizedHyperplaneTransitions

/-! # Hyperplane sections glued on the original normalized affine cover

The gluing condition is equality of actual regular coefficients on the
actual normalized overlaps, using the constructed coordinate transition
unit. It is equivalent to the common-field representation used by the
section degree bound.
-/

namespace DimensionFourDependence

variable {k F : Type*} [Field k] [Field F] [Algebra k F]

/-- Global hyperplane-section gluing data on the four original normalized
charts, with equality on their actual normalized overlaps. -/
structure NormalizedHyperplaneGluingSection (x : Fin 4 → F) (hx : ∀ i, x i ≠ 0) where
  coefficient (i : Fin 4) : integralClosure (projectiveCoordinateChartAlgebra (C := k) x i) F
  transition (i j : Fin 4) : normalizedProjectiveOverlapLeft x i j (coefficient i) =
    (normalizedHyperplaneTransitionUnit (k := k) x i j (hx i) (hx j) :
      integralClosure (projectiveChartOverlap (C := k) x i j) F) *
        normalizedProjectiveOverlapRight x i j (hx i) (hx j) (coefficient j)

/-- Actual overlap gluing supplies the original common-field section
coefficients and transition equations, without assuming them separately. -/
noncomputable def NormalizedHyperplaneGluingSection.toProjective
    {x : Fin 4 → F} {hx : ∀ i, x i ≠ 0}
    (s : NormalizedHyperplaneGluingSection (k := k) x hx) : ProjectiveNormalizedSection (k := k) x where
  coefficient := s.coefficient
  transition i j := (normalized_hyperplane_overlap_transition_iff x i j (hx i) (hx j) _ _).mp
    (s.transition i j)

/-- The original common-field representation yields genuine equalities
of regular coefficients on the actual normalized chart overlaps. -/
noncomputable def ProjectiveNormalizedSection.toNormalizedGluing
    {x : Fin 4 → F} (s : ProjectiveNormalizedSection (k := k) x) (hx : ∀ i, x i ≠ 0) :
    NormalizedHyperplaneGluingSection (k := k) x hx where
  coefficient := s.coefficient
  transition i j := (normalized_hyperplane_overlap_transition_iff x i j (hx i) (hx j) _ _).mpr
    (s.transition i j)

/-- The two section descriptions agree on every original normalized
chart coefficient and give inverse global gluing representations. -/
noncomputable def normalizedHyperplaneGluingSectionEquiv
    (x : Fin 4 → F) (hx : ∀ i, x i ≠ 0) :
    NormalizedHyperplaneGluingSection (k := k) x hx ≃ ProjectiveNormalizedSection (k := k) x where
  toFun := NormalizedHyperplaneGluingSection.toProjective
  invFun := fun s => s.toNormalizedGluing hx
  left_inv := by intro s; cases s; rfl
  right_inv := by intro s; cases s; rfl

/-- The gluing equivalence retains every original rational coefficient. -/
theorem normalizedHyperplaneGluingSectionEquiv_coefficient
    (x : Fin 4 → F) (hx : ∀ i, x i ≠ 0)
    (s : NormalizedHyperplaneGluingSection (k := k) x hx) (i : Fin 4) :
    (normalizedHyperplaneGluingSectionEquiv x hx s).coefficient i = s.coefficient i := rfl

end DimensionFourDependence
