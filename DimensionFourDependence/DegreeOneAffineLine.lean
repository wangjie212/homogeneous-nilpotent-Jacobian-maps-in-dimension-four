import DimensionFourDependence.AffineTwoCoordinateLine
import DimensionFourDependence.PlaneEquationDegreeBound
import DimensionFourDependence.CoordinateProjectionHilbert
import DimensionFourDependence.AffineLineDerivation

/-! # A curve of actual Hilbert degree one is an affine line

Project to a transcendental coordinate and each other coordinate. The
entire projected closure is a principal plane curve. Its nonzero
homogeneous equation has degree at most the original Hilbert degree,
so degree one gives an actual affine-linear expression for every
coordinate. Nonlinearity consequently forces degree at least two.
-/

namespace DimensionFourDependence

open MvPolynomial

variable {L F sigma : Type*} [Field L] [Field F] [Algebra L F]

/-- Every coordinate of a degree-one curve is an actual affine-linear
function of any one of its transcendental source coordinates. -/
theorem degree_one_coordinate_affine_expression [Finite sigma]
    (x : sigma → F) (i j : sigma) (ht : Transcendental L (x i))
    (he : HasCurveHilbertDegree (projectiveConeIdeal (L := L) x) 1) :
    ∃ a b : L, x j = algebraMap L F a + algebraMap L F b * x i := by
  let f : Option Unit → sigma := fun k => k.elim j (fun _ => i)
  let pair : Option Unit → F := fun k => k.elim (x j) (fun _ => x i)
  have hpair : pair = x ∘ f := by funext k; cases k <;> rfl
  obtain ⟨P, d, hP, hideal⟩ := two_coordinate_projective_closure_exists_homogeneous_generator
    (x i) (x j) ht
  have hcard : Nat.card (Option (Option Unit)) = 3 := by simp
  have hbound : ∀ n, projectiveHilbertFunction (Ideal.span {P}) n ≤
      projectiveHilbertFunction (projectiveConeIdeal (L := L) x) n := by
    intro n
    rw [← hideal]
    change projectiveHilbertFunction (projectiveConeIdeal (L := L) pair) n ≤ _
    rw [hpair]
    exact projectiveHilbertFunction_coordinate_projection_le x f n
  have hP0 : P ≠ 0 := plane_principal_equation_ne_zero_of_curve_hilbert_bound
    hcard P _ he hbound
  have hd : d ≤ 1 := plane_principal_equation_degree_le_curve_degree hcard P hP hP0 _ he hbound
  let Q := projectiveDehomogenize P
  have hQ0 : Q ≠ 0 := by
    intro hzero
    exact hP0 (homogeneous_dehomogenize_eq_zero P hP hzero)
  have hQ : Q.totalDegree ≤ 1 := (projectiveDehomogenize_totalDegree P).trans (hP.totalDegree_le.trans hd)
  have hvalue : aeval pair Q = 0 := by
    rw [← aeval_projectiveDehomogenize]
    apply (projectiveConeIdeal_mem_of_isHomogeneous pair hP).mp
    rw [hideal]
    exact Ideal.subset_span (by simp)
  exact affine_two_coordinate_relation_solve (x i) (x j) ht Q hQ0 hQ hvalue

variable {n : ℕ}

/-- A degree-one curve lies on an actual affine line over the
original coefficient field, with a nonzero direction constructed from
its transcendental coordinate. -/
theorem degree_one_curve_liesInAffineLine
    (x : Fin n → F) (i : Fin n) (ht : Transcendental L (x i))
    (he : HasCurveHilbertDegree (projectiveConeIdeal (L := L) x) 1) :
    LiesInAffineLine (E := L) x := by
  classical
  choose a b hab using fun j => degree_one_coordinate_affine_expression x i j ht he
  refine ⟨a, b, ?_, x i, hab⟩
  intro hzero
  apply ht
  have heq := hab i
  rw [show b i = 0 from congrFun hzero i, map_zero, zero_mul, add_zero] at heq
  rw [heq]
  exact isAlgebraic_algebraMap (a i)

/-- A nonlinear affine curve has actual Hilbert degree at least two. -/
theorem nonlinear_curve_hilbert_degree_at_least_two
    (x : Fin n → F) (i : Fin n) (ht : Transcendental L (x i))
    {e : ℕ} (he : HasCurveHilbertDegree (projectiveConeIdeal (L := L) x) e)
    (hline : ¬ LiesInAffineLine (E := L) x) : 2 ≤ e := by
  by_contra hsmall
  have he1 : e = 1 := by have := he.1; omega
  subst e
  exact hline (degree_one_curve_liesInAffineLine x i ht he)

/-- The global degree bound by two is exact for a nonlinear curve. -/
theorem nonlinear_curve_hilbert_degree_eq_two
    (x : Fin n → F) (i : Fin n) (ht : Transcendental L (x i))
    {e : ℕ} (he : HasCurveHilbertDegree (projectiveConeIdeal (L := L) x) e)
    (hline : ¬ LiesInAffineLine (E := L) x) (hupper : e ≤ 2) : e = 2 :=
  Nat.le_antisymm hupper (nonlinear_curve_hilbert_degree_at_least_two x i ht he hline)

end DimensionFourDependence
