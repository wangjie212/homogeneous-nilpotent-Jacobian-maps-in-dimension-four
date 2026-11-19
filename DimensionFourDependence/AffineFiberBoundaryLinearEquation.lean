import DimensionFourDependence.ProjectiveClosureLeadingEquations
import DimensionFourDependence.ModifiedCubicFiberBoundary

/-! # An actual affine linear fiber equation gives its original covector at every infinity point -/

namespace DimensionFourDependence

open MvPolynomial Matrix
attribute [local instance] MvPolynomial.gradedAlgebra

variable {E F κ σ : Type*} [Field E] [Field F] [Field κ] [Algebra E F] [Algebra E κ]

/-- Leading-degree comparison of the actual affine linear equation
retains the original covector at every actual projective infinity point. -/
theorem affine_linear_fiber_equation_covector_vanishes_at_infinity {n : ℕ}
    (x : σ → F) (z : Option σ → κ) (hz : z ≠ 0)
    (hpoint : projectiveFieldPoint (E := E) z hz ∈ projectiveClosureSet (L := E) x)
    (hz0 : z none = 0) (f : Fin n → σ) (a : Fin n → E) (c : E)
    (he : algebraMap E F c = (fun i => algebraMap E F (a i)) ⬝ᵥ (x ∘ f)) :
    (fun i => algebraMap E κ (a i)) ⬝ᵥ (fun i => z (some (f i))) = 0 := by
  let P := linearFormPolynomial a - C c
  have hPdeg : P.totalDegree ≤ 1 := (totalDegree_sub_C_le _ _).trans (linearFormPolynomial_totalDegree a)
  have hPvalue : aeval (x ∘ f) P = 0 := by
    simp only [P, map_sub, aeval_C, linearFormPolynomial, map_sum, map_mul, aeval_X]
    exact sub_eq_zero.mpr he.symm
  have hconst : homogeneousComponent 1 (C c : MvPolynomial (Fin n) E) = 0 :=
    homogeneousComponent_eq_zero 1 _ (by simp)
  have hleading : homogeneousComponent 1 P = linearFormPolynomial a := by
    rw [show P = linearFormPolynomial a - C c from rfl, map_sub,
      homogeneousComponent_eq_self (linearFormPolynomial_homogeneous a), hconst, sub_zero]
  have hb := projectiveClosureSet_projected_leading_equation_at_infinity x z hz hpoint hz0 f P 1 hPdeg hPvalue
  rw [hleading] at hb
  simpa only [linearFormPolynomial, map_sum, map_mul, aeval_C, aeval_X, dotProduct] using hb

end DimensionFourDependence
