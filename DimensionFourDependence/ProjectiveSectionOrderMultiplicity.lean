import DimensionFourDependence.ProjectivePointCommonFactor
import DimensionFourDependence.IntrinsicDivisorPullback

/-! # Common-factor degree from geometric homogeneous-section orders

The order hypothesis uses the actual geometric stalk pullback in a
standard regular frame at the source point. An intrinsic divisor
comparison turns these into orders on the original projective source.
-/

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

/-- Every original homogeneous section has the specified regular order
after actual geometric pullback, in a standard frame at the source point.
The frame and its nonvanishing coordinate are part of the witness. -/
def ProjectiveSourceSectionOrders {Y : Scheme.{u}} (f : Y ⟶ Pₖ)
    (y : Y) (H : Fin 4 → R₄) (a : ℕ) : Prop :=
  ∃ (s : Fin 4 ≃ Option (Fin 3))
    (hy : f y ∈ Proj.basicOpen (homogeneousSubmodule (Fin 4) K) (X (s.symm none))),
      ∀ i, f.stalkMap y ((Pₖ).presheaf.germ
        (Proj.basicOpen (homogeneousSubmodule (Fin 4) K) (X (s.symm none))) (f y) hy
          ((originalProjectiveAffineSectionEquiv (K := K) (s.symm none)).symm
            (projectiveSourceSectionHom s (H i)))) ∈
        (IsLocalRing.maximalIdeal (Y.presheaf.stalk y)) ^ a

/-- Equality of intrinsic source-divisor orders converts the actual
pulled-back homogeneous section orders into a divisor power in the
original homogeneous common factor and the required degree bound. -/
theorem geometric_projective_section_orders_common_factor_degree
    {Y : Scheme.{u}} (f : Y ⟶ Pₖ) (y : Y)
    (hcodim : Order.coheight (f y) = 1)
    (hcomparison : IntrinsicDivisorPullbackComparison (f.stalkMap y).hom)
    (H P : Fin 4 → R₄) (g : R₄) {c d : ℕ}
    (hg : g ≠ 0) (hgh : g.IsHomogeneous c) (hP : IsHomogMap P d)
    (hprim : IsPrimitiveVec P) (hHP : H = fun i => g * P i)
    (a : ℕ) (horder : ProjectiveSourceSectionOrders f y H a) :
    ∃ Δ : R₄, Irreducible Δ ∧ Δ.IsHomogeneous Δ.totalDegree ∧
      Δ ^ a ∣ g ∧ a * Δ.totalDegree ≤ g.totalDegree ∧ a ≤ g.totalDegree := by
  obtain ⟨s, hy, horder⟩ := horder
  obtain ⟨_hS, _hA, _hDVR, _hframed, hregular⟩ := hcomparison
  apply projective_source_point_orders_common_factor_degree
    s H P g hg hgh hP hprim hHP (f y) hy hcodim a
  intro i
  exact (hregular _ a).mp (horder i)

end DimensionFourDependence
