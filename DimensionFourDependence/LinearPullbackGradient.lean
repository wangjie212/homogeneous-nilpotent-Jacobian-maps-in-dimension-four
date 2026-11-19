import DimensionFourDependence.LinearPolynomialCoordinates

/-! # Gradients under invertible actual linear coordinates

The chain rule gives the evaluated gradient row of a linear pullback.
An invertible coordinate map preserves whether that row is zero, proved
by testing it on inverse images of the actual coordinate basis vectors.
-/

namespace DimensionFourDependence

open MvPolynomial Matrix

variable {F : Type*} [Field F]

/-- The actual evaluated gradient row of a linear polynomial pullback. -/
theorem linearPolynomialPullback_gradient
    (A : Matrix (Fin 4) (Fin 4) F) (R : MvPolynomial (Fin 4) F) (x : Fin 4 → F) :
    (fun i => aeval x (pderiv i (linearPolynomialPullback A R))) =
      (fun j => aeval (A *ᵥ x) (pderiv j R)) ᵥ* A := by
  have hder (j i : Fin 4) : pderiv i (linearPolynomialMap A j) = MvPolynomial.C (A j i) := by
    change (jac (linearPolynomialMap A)) j i = _
    rw [jac_linearPolynomialMap]
    rfl
  funext i
  rw [linearPolynomialPullback, pderiv_aeval, map_sum]
  simp only [map_mul, hder, aeval_C, Algebra.algebraMap_self_apply]
  simp_rw [comp_aeval_apply, linearPolynomialMap_aeval]
  rfl

/-- Invertible linear coordinates preserve vanishing of the actual
evaluated gradient, with no matrix nonsingularity left to assume. -/
theorem linearPolynomialPullback_gradient_zero_iff
    (g : (Fin 4 → F) ≃ₗ[F] (Fin 4 → F)) (R : MvPolynomial (Fin 4) F) (x : Fin 4 → F) :
    (fun i => aeval x (pderiv i (linearPolynomialPullback (LinearMap.toMatrix' g.toLinearMap) R))) = 0 ↔
      (fun j => aeval (g x) (pderiv j R)) = 0 := by
  let A := LinearMap.toMatrix' g.toLinearMap
  have hAx : A *ᵥ x = g x := by
    change (Matrix.toLin' (LinearMap.toMatrix' g.toLinearMap)) x = g x
    rw [Matrix.toLin'_toMatrix']
    rfl
  rw [linearPolynomialPullback_gradient, hAx]
  constructor
  · intro hz
    funext j
    let v := g.symm (Pi.single j 1)
    have hAv : A *ᵥ v = Pi.single j 1 := by
      change (Matrix.toLin' (LinearMap.toMatrix' g.toLinearMap)) v = _
      rw [Matrix.toLin'_toMatrix']
      exact g.apply_symm_apply _
    have he := congrArg (fun w : Fin 4 → F => w ⬝ᵥ v) hz
    rw [← dotProduct_mulVec, hAv] at he
    simpa [dotProduct, Pi.single_apply] using he
  · intro hz
    rw [hz, zero_vecMul]

end DimensionFourDependence
