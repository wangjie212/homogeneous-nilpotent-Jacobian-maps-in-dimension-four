import DimensionFourDependence.AffineCoordinateGeneration
import DimensionFourDependence.NormalizedAffineCoordinateMultiplicity

/-! # The original hypersurface degree bounds affine hyperplane orders

An affine hyperplane with a nonzero pivot coefficient replaces one
original generator. The constructed inverse preserves the original
equation's nonzero status and degree, so the coordinate multiplicity
bound applies to that exact linear section on the canonical normalization.
-/

namespace DimensionFourDependence

universe u

open MvPolynomial

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 2000000

variable {k A : Type u} [Field k] [CharZero k]
  [CommRing A] [IsDomain A] [Algebra k A] [Algebra.FiniteType k A]

/-- The original hypersurface degree bounds the order of the given
nonzero affine linear section, with the new generators, inverse equation
and degree estimate all constructed from the original coordinates. -/
theorem canonical_normalization_affine_pivot_order_le_totalDegree
    (x : Option (Option Unit) → A) (hx : Algebra.adjoin k (Set.range x) = ⊤)
    (htr : 2 ≤ Algebra.trdeg k A)
    (b : k) (c : Option (Option Unit) → k) (hc : c (some none) ≠ 0)
    (f : MvPolynomial (Option (Option Unit)) k) (hf : f ≠ 0)
    (hroot : aeval x f = 0)
    (Q : Ideal (normalizationRing A)) [Q.IsPrime] (hQ : Q.height = 1)
    (hz0 : affinePivotCoordinate x (some none) (c (some none)) b c (some none) ≠ 0)
    (hz : algebraMap A (normalizationRing A)
      (affinePivotCoordinate x (some none) (c (some none)) b c (some none)) ∈ Q)
    (a : ℕ) (horder : algebraMap A (Localization.AtPrime Q)
      (affinePivotCoordinate x (some none) (c (some none)) b c (some none)) ∈
        (IsLocalRing.maximalIdeal (Localization.AtPrime Q)) ^ a) :
    a ≤ f.totalDegree := by
  let j : Option (Option Unit) := some none
  let y := affinePivotCoordinate x j (c j) b c
  let g := affinePivotInverseSubstitution j (c j) b c
  have hy : Algebra.adjoin k (Set.range y) = ⊤ :=
    affinePivotCoordinate_adjoin_eq_top x hx j (c j) b c hc
  have hgf : g f ≠ 0 := by
    intro hzero
    apply hf
    apply affinePivotInverseSubstitution_injective j (c j) b c hc
    simpa only [map_zero] using hzero
  have hroot' : aeval y (g f) = 0 :=
    (affinePivotCoordinate_eval_inverse x j (c j) b c hc f).trans hroot
  have h := canonical_normalization_coordinate_order_le_totalDegree
    (k := k) y hy htr Q hQ hz0 hz (g f) hgf hroot' a horder
  exact h.trans (affinePivotInverseSubstitution_totalDegree_le j (c j) b c f)

end DimensionFourDependence
