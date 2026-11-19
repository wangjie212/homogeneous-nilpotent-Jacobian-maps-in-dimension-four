import DimensionFourDependence.AffineCoordinateStalk
import Mathlib.RingTheory.Ideal.Height

/-! # Intrinsic codimension in actual affine stalks -/

namespace DimensionFourDependence

open AlgebraicGeometry

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The dimension of the actual scheme stalk is the height of its
prime in any affine neighborhood. -/
theorem affineOpen_stalk_dimension_eq_prime_height
    {X : Scheme.{u}} (U : X.affineOpens) (x : U.1) :
    ringKrullDim (X.presheaf.stalk x.1) = (U.2.primeIdealOf x).asIdeal.height := by
  let : Algebra Γ(X, U.1) (X.presheaf.stalk x.1) :=
    X.presheaf.algebra_section_stalk x
  let : IsLocalization.AtPrime (X.presheaf.stalk x.1) (U.2.primeIdealOf x).asIdeal :=
    U.2.isLocalization_stalk x
  exact IsLocalization.AtPrime.ringKrullDim_eq_height
    (U.2.primeIdealOf x).asIdeal (X.presheaf.stalk x.1)

end DimensionFourDependence
