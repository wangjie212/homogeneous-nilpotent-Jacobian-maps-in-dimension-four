import DimensionFourDependence.MultivariateHomogenize

/-! # Recovering affine values and gradients on the projective chart -/

namespace DimensionFourDependence

open MvPolynomial

variable {R σ : Type*} [Field R]

/-- Dehomogenization commutes with differentiation in an affine variable. -/
theorem projectiveDehomogenize_pderiv (p : MvPolynomial (Option σ) R) (i : σ) :
    projectiveDehomogenize (pderiv (some i) p) = pderiv i (projectiveDehomogenize p) := by
  classical
  induction p using MvPolynomial.induction_on with
  | C a => simp [projectiveDehomogenize]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p j hp =>
    cases j <;> simp [pderiv_X, Pi.single_apply, hp, apply_ite,
      projectiveDehomogenize_X_none, projectiveDehomogenize_X_some]

variable {A : Type*} [Field A] [Algebra R A]

/-- Evaluating a homogeneous-coordinate polynomial on the chart with
first coordinate one is evaluation of its dehomogenization. -/
theorem aeval_projectiveDehomogenize (x : σ → A) (p : MvPolynomial (Option σ) R) :
    aeval (fun j : Option σ => j.elim 1 x) p = aeval x (projectiveDehomogenize p) := by
  have he : (aeval x).comp (projectiveDehomogenize (R := R) (σ := σ)) =
      aeval (fun j : Option σ => j.elim 1 x) := by
    apply MvPolynomial.algHom_ext
    intro j
    cases j <;> simp [projectiveDehomogenize]
  exact (DFunLike.congr_fun he p).symm

/-- The homogenized equation has precisely the original values on the affine chart. -/
theorem projectiveHomogenize_aeval_chart (p : MvPolynomial σ R) (d : ℕ) (x : σ → A) :
    aeval (fun j : Option σ => j.elim 1 x) (projectiveHomogenize p d) = aeval x p := by
  rw [aeval_projectiveDehomogenize, projectiveDehomogenize_homogenize]

/-- The affine components of the homogeneous polynomial gradient agree
with the original polynomial gradient on this chart. -/
theorem projectiveHomogenize_gradient_aeval_chart
    (p : MvPolynomial σ R) (d : ℕ) (x : σ → A) (i : σ) :
    aeval (fun j : Option σ => j.elim 1 x) (pderiv (some i) (projectiveHomogenize p d)) =
      aeval x (pderiv i p) := by
  rw [aeval_projectiveDehomogenize, projectiveDehomogenize_pderiv,
    projectiveDehomogenize_homogenize]

end DimensionFourDependence
