import DimensionFourDependence.ProjectiveSectionOrderMultiplicity
import DimensionFourDependence.SchemeRegularOrderBounds

/-! # Homogeneous-section bounds in actual integer scheme orders -/

namespace DimensionFourDependence

open AlgebraicGeometry MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {K : Type u} [Field K]

local notation "Pₖ" => AlgebraicGeometry.Proj (homogeneousSubmodule (Fin 4) K)
local notation "R₄" => MvPolynomial (Fin 4) K

/-- Homogeneous-section bounds expressed in the target scheme's own
function field and integer order. Zero section coefficients satisfy
every bound explicitly, since Mathlib gives them junk integer order zero. -/
def ProjectiveSourceSectionIntegerOrders
    {Y : Scheme.{u}} [IsIntegral Y] [IsLocallyNoetherian Y]
    (f : Y ⟶ Pₖ) (y : Y) (H : Fin 4 → R₄) (a : ℕ) : Prop :=
  ∃ (s : Fin 4 ≃ Option (Fin 3))
    (hy : f y ∈ Proj.basicOpen (homogeneousSubmodule (Fin 4) K) (X (s.symm none))),
      ∀ i, let z := f.stalkMap y ((Pₖ).presheaf.germ
        (Proj.basicOpen (homogeneousSubmodule (Fin 4) K) (X (s.symm none))) (f y) hy
          ((originalProjectiveAffineSectionEquiv (K := K) (s.symm none)).symm
            (projectiveSourceSectionHom s (H i))))
        z = 0 ∨ (a : ℤ) ≤ Y.ord (algebraMap (Y.presheaf.stalk y) Y.functionField z) y

/-- At a divisor DVR the integer scheme-order statement is equivalent
to the actual regular local-section order statement in the same frame. -/
theorem projective_source_section_integer_orders_iff
    {Y : Scheme.{u}} [IsIntegral Y] [IsLocallyNoetherian Y]
    (f : Y ⟶ Pₖ) (y : Y) (hy : Order.coheight y = 1)
    [IsDiscreteValuationRing (Y.presheaf.stalk y)] (H : Fin 4 → R₄) (a : ℕ) :
    ProjectiveSourceSectionIntegerOrders f y H a ↔ ProjectiveSourceSectionOrders f y H a := by
  constructor
  · rintro ⟨s, hs, horder⟩
    refine ⟨s, hs, ?_⟩
    intro i
    exact (scheme_regular_order_bound_iff (X := Y) y hy _ a).mp (horder i)
  · rintro ⟨s, hs, horder⟩
    refine ⟨s, hs, ?_⟩
    intro i
    exact (scheme_regular_order_bound_iff (X := Y) y hy _ a).mpr (horder i)

end DimensionFourDependence
