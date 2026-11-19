import DimensionFourDependence.PrimitiveBoundaryImage
import DimensionFourDependence.BoundaryIsotropicEquations

/-! # Leading equations at arbitrary actual projective boundary points

An equation in any selected affine coordinates homogenizes to an
equation of the full actual projective closure. On its infinity
hyperplane only the leading homogeneous component remains. This works
at arbitrary extension-field coordinates, without a valuation lift.
-/

namespace DimensionFourDependence

open MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra

variable {E F κ σ τ : Type*} [Field E] [Field F] [Field κ]
    [Algebra E F] [Algebra E κ]

/-- Leading parts of equations in selected coordinates vanish at
every actual full projective-closure point on the infinity hyperplane. -/
theorem projectiveClosureSet_projected_leading_equation_at_infinity
    (x : σ → F) (z : Option σ → κ) (hz : z ≠ 0)
    (hpoint : projectiveFieldPoint (E := E) z hz ∈ projectiveClosureSet (L := E) x)
    (hz0 : z none = 0) (f : τ → σ) (P : MvPolynomial τ E) (d : ℕ)
    (hd : P.totalDegree ≤ d) (hzero : aeval (x ∘ f) P = 0) :
    aeval (fun i => z (some (f i))) (homogeneousComponent d P) = 0 := by
  let T := rename (Option.map f) (projectiveHomogenize P d)
  have hT : T.IsHomogeneous d := (projectiveHomogenize_isHomogeneous P d hd).rename_isHomogeneous
  have hvan : T ∈ projectiveConeIdeal (L := E) x := by
    apply (projectiveConeIdeal_mem_of_isHomogeneous x hT).mpr
    rw [show T = rename (Option.map f) (projectiveHomogenize P d) from rfl, aeval_rename]
    have hc : (fun j : Option σ => j.elim 1 x) ∘ Option.map f =
        (fun j : Option τ => j.elim 1 (x ∘ f)) := by
      funext j
      cases j <;> rfl
    rw [hc]
    rw [projectiveHomogenize_aeval_chart]
    exact hzero
  have he := projectiveClosureSet_extension_coordinate_equation x z hz hpoint hT hvan
  rw [show T = rename (Option.map f) (projectiveHomogenize P d) from rfl, aeval_rename] at he
  have hcoords : z ∘ Option.map f =
      (fun j : Option τ => j.elim 0 (fun i => z (some (f i)))) := by
    funext j
    cases j <;> simp [hz0]
  rw [hcoords, projectiveHomogenize_aeval_at_infinity P d hd] at he
  exact he

variable [CharZero E] {n : ℕ}

/-- The quadratic fiber equation forces Hessian isotropy at every
actual boundary point, including points without a chosen valuation lift. -/
theorem projective_fiber_closure_quadratic_isotropic
    (x : σ → F) (z : Option σ → κ) (hz : z ≠ 0)
    (hpoint : projectiveFieldPoint (E := E) z hz ∈ projectiveClosureSet (L := E) x)
    (hz0 : z none = 0) (f : Fin n → σ)
    (a : Fin n → E) (T : Matrix (Fin n) (Fin n) E) (q : E)
    (hQ : aeval (x ∘ f) (quadraticFiberPolynomial a T q) = 0) :
    matrixBilinearPairing (T.map (algebraMap E κ))
      (fun i => z (some (f i))) (fun i => z (some (f i))) = 0 := by
  have he := projectiveClosureSet_projected_leading_equation_at_infinity x z hz hpoint hz0 f
    (quadraticFiberPolynomial a T q) 2 (quadraticFiberPolynomial_totalDegree a T q) hQ
  rw [quadraticFiberPolynomial_leading_component, map_mul, aeval_C] at he
  have hhalf : algebraMap E κ ((2 : E)⁻¹) ≠ 0 :=
    (map_ne_zero (algebraMap E κ)).mpr (inv_ne_zero (by norm_num))
  have hform := (mul_eq_zero.mp he).resolve_left hhalf
  simpa only [quadraticFormPolynomial, map_sum, map_mul, aeval_C, aeval_X,
    matrixBilinearPairing, Matrix.map_apply] using hform

end DimensionFourDependence
