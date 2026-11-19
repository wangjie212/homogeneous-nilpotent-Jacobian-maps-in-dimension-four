import DimensionFourDependence.RationalInfinityDegree

/-! # The actual infinity valuation ring acts through the given projection field

This constructs the infinity-base action on the specified function field
from its actual rational projection action. Both coefficient maps are the
original maps, so the norm-degree argument needs no independently chosen
infinity-ring action or compatibility hypothesis.
-/

namespace DimensionFourDependence

variable {k L : Type*} [Field k] [Field L] [Algebra (RatFunc k) L]

/-- The actual infinity-ring action through the given rational
projection field embedding. -/
@[instance_reducible]
noncomputable def rationalInfinityTargetAlgebra : Algebra (rationalInfinityRing k) L :=
  ((algebraMap (RatFunc k) L).comp
    (algebraMap (rationalInfinityRing k) (RatFunc k))).toAlgebra

/-- The constructed infinity action retains every original rational value. -/
theorem rationalInfinityTargetAlgebra_algebraMap (x : rationalInfinityRing k) :
    let : Algebra (rationalInfinityRing k) L := rationalInfinityTargetAlgebra
    algebraMap (rationalInfinityRing k) L x = algebraMap (RatFunc k) L (x : RatFunc k) := rfl

/-- The actual infinity-base action and rational projection action are
compatible through their specified field inclusion. -/
theorem rationalInfinityTargetAlgebra_scalarTower :
    let : Algebra (rationalInfinityRing k) L := rationalInfinityTargetAlgebra
    IsScalarTower (rationalInfinityRing k) (RatFunc k) L := by
  let : Algebra (rationalInfinityRing k) L := rationalInfinityTargetAlgebra
  exact IsScalarTower.of_algebraMap_eq (fun _ => rfl)

end DimensionFourDependence
