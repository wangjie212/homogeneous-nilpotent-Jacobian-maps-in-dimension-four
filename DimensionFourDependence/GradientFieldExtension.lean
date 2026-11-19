import DimensionFourDependence.ScalarExtendedImageEquation

/-! # Descent of projective nonsingularity along a coefficient field map -/

namespace DimensionFourDependence

open MvPolynomial

variable {K F σ : Type*} [Field K] [Field F] [Algebra K F]

/-- Evaluating an extended partial derivative at an extended original
point is the original derivative value mapped to the larger field. -/
theorem pderiv_aeval_map_coefficients (R : MvPolynomial σ K) (x : σ → K) (i : σ) :
    aeval (fun j => algebraMap K F (x j)) (pderiv i (MvPolynomial.map (algebraMap K F) R)) =
      algebraMap K F (aeval x (pderiv i R)) := by
  rw [MvPolynomial.pderiv_map]
  change MvPolynomial.eval ((algebraMap K F) ∘ x) (MvPolynomial.map (algebraMap K F) (pderiv i R)) =
    algebraMap K F (MvPolynomial.eval x (pderiv i R))
  exact (MvPolynomial.map_eval (algebraMap K F) x (pderiv i R)).symm

/-- Nonsingularity at every nonzero vector over an extended field
implies nonsingularity at every original-field nonzero vector. -/
theorem projective_gradient_nonvanishing_descends (R : MvPolynomial σ K)
    (h : ∀ x : σ → F, x ≠ 0 →
      (fun i => aeval x (pderiv i (MvPolynomial.map (algebraMap K F) R))) ≠ 0) :
    ∀ x : σ → K, x ≠ 0 → (fun i => aeval x (pderiv i R)) ≠ 0 := by
  intro x hx hz
  apply h (fun i => algebraMap K F (x i))
  · intro he
    apply hx
    funext i
    apply (algebraMap K F).injective
    simpa only [map_zero, Pi.zero_apply] using congrFun he i
  · funext i
    rw [pderiv_aeval_map_coefficients]
    have hi := congrFun hz i
    simp only [Pi.zero_apply] at hi
    rw [hi, map_zero]
    rfl

end DimensionFourDependence
