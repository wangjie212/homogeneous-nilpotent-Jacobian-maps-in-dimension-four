import DimensionFourDependence.SchemeRegularOrderBounds

/-! # The actual integer divisor order is independent of every regular local frame -/

namespace DimensionFourDependence

open AlgebraicGeometry

/-- Every regular frame change has integer divisor order zero and
preserves the actual scheme order of every rational coefficient. This
includes zero coefficients with Mathlib's assigned order value. -/
theorem scheme_rational_regular_frame_integer_order
    {X : Scheme} [IsIntegral X] [IsLocallyNoetherian X]
    (y : X) (hy : Order.coheight y = 1)
    (u : (X.presheaf.stalk y)ˣ) (f : X.functionField) :
    X.ord (algebraMap (X.presheaf.stalk y) X.functionField
      (u : X.presheaf.stalk y) * f) y = X.ord f y := by
  let : Ring.KrullDimLE 1 (X.presheaf.stalk y) := krullDimLE_of_coheight_le hy.le
  rw [Scheme.ord_eq_ordHom_of_coheight_eq_one hy,
    Scheme.ord_eq_ordHom_of_coheight_eq_one hy]
  change Multiplicative.toAdd ((Ring.ordFrac (X.presheaf.stalk y)
    (algebraMap (X.presheaf.stalk y) X.functionField (u : X.presheaf.stalk y) * f)).unzeroD 1) =
      Multiplicative.toAdd ((Ring.ordFrac (X.presheaf.stalk y) f).unzeroD 1)
  rw [map_mul, Ring.ordFrac_of_isUnit u.isUnit, one_mul]

/-- A regular coefficient's actual integer multiplicity is unchanged
when its regular local frame is multiplied by any unit. -/
theorem scheme_regular_coefficient_frame_integer_order
    {X : Scheme} [IsIntegral X] [IsLocallyNoetherian X]
    (y : X) (hy : Order.coheight y = 1)
    (u : (X.presheaf.stalk y)ˣ) (z : X.presheaf.stalk y) :
    X.ord (algebraMap (X.presheaf.stalk y) X.functionField
      ((u : X.presheaf.stalk y) * z)) y =
        X.ord (algebraMap (X.presheaf.stalk y) X.functionField z) y := by
  rw [map_mul]
  exact scheme_rational_regular_frame_integer_order y hy u _

end DimensionFourDependence
