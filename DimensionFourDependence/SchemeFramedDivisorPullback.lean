import DimensionFourDependence.SchemeDivisorPullback

/-! # Actual scheme-function-field pullbacks in every regular local frame -/

namespace DimensionFourDependence

open AlgebraicGeometry

universe u

/-- A geometric divisor comparison gives a single actual rational
pullback preserving integer orders in every regular source-stalk frame. -/
theorem scheme_divisor_pullback_all_regular_frames
    {X Y : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    [IsIntegral Y] [IsLocallyNoetherian Y]
    (f : Y ⟶ X) (y : Y) (h : SchemeDivisorPullbackComparison f y) :
    ∃ hx : Order.coheight (f y) = 1, ∃ hy : Order.coheight y = 1,
      ∃ j : X.functionField →+* Y.functionField,
        (∀ z : X.presheaf.stalk (f y),
          j (algebraMap (X.presheaf.stalk (f y)) X.functionField z) =
            algebraMap (Y.presheaf.stalk y) Y.functionField (f.stalkMap y z)) ∧
        (∀ x : X.functionField, X.ord x (f y) = Y.ord (j x) y) ∧
        ∀ (v : (X.presheaf.stalk (f y))ˣ) (x : X.functionField),
          Y.ord (j (algebraMap (X.presheaf.stalk (f y)) X.functionField
            (v : X.presheaf.stalk (f y)) * x)) y = X.ord x (f y) := by
  obtain ⟨hx, hy, j, hj, horder⟩ := h
  refine ⟨hx, hy, j, hj, horder, ?_⟩
  exact scheme_source_rational_section_frame_order f y hx j horder

end DimensionFourDependence
