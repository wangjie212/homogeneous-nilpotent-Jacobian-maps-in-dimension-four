import DimensionFourDependence.AffineHyperplane
import DimensionFourDependence.TranscendentalPolynomialParametrization

/-! # A vertex-dependent affine parameter cannot be constant on a nonlinear parabola

Clearing the actual nonzero chart denominator turns a constant affine
parameter into a linear source-coordinate relation. Evaluation on the
actual transcendental parabolic parameter makes its entire polynomial
zero. Its quadratic coefficient is the nonzero vertex coefficient times
the nonzero quadratic coefficient of the parabola, a contradiction.
-/

namespace DimensionFourDependence

open MvPolynomial

set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 100000

variable {K E G : Type*} [Field K] [Field E] [Field G]
    [Algebra K E] [Algebra K G] [Algebra E G] [IsScalarTower K E G]

/-- A nonzero vertex partial of an affine polynomial is a nonzero
original-field scalar coefficient. -/
theorem affine_polynomial_nonzero_vertex_coefficient
    (P : MvPolynomial (Fin 3) K) (hP : P.totalDegree ≤ 1)
    (hPw : pderiv (2 : Fin 3) P ≠ 0) : (pderiv (2 : Fin 3) P).coeff 0 ≠ 0 := by
  intro hz
  apply hPw
  rw [affine_pderiv_eq_C P hP, hz, map_zero]

/-- An affine parameter with nonzero vertex partial cannot be constant
on an actual nonlinear vertex parabola whose chart denominator is nonzero.
The relation is proved at the actual source point, with no formal curve
identity assumed. -/
theorem affine_parameter_constant_on_nonlinear_vertex_parabola_impossible
    (P : MvPolynomial (Fin 3) K) (hP : P.totalDegree ≤ 1) (hPw : pderiv (2 : Fin 3) P ≠ 0)
    (t : G) (ht : Transcendental E t) (z : Fin 4 → G)
    (x A : Fin 3 → E) (w0 B C c : E) (hC : C ≠ 0)
    (hx : ∀ i : Fin 3, z i.castSucc = algebraMap E G (x i) + algebraMap E G (A i) * t)
    (hw : z (Fin.last 3) = algebraMap E G w0 + algebraMap E G B * t + algebraMap E G C * t ^ 2)
    (hy : z 1 ≠ 0)
    (hvalue : aeval (![z 0 / z 1, z 2 / z 1, z 3 / z 1] : Fin 3 → G) P = algebraMap E G c) :
    False := by
  let a : Fin 3 → K := fun i => (pderiv i P).coeff 0
  let l : Fin 3 → Polynomial E := fun i => Polynomial.C (x i) + Polynomial.C (A i) * Polynomial.X
  let w : Polynomial E := Polynomial.C w0 + Polynomial.C B * Polynomial.X + Polynomial.C C * Polynomial.X ^ 2
  let Q : Polynomial E :=
    Polynomial.C (algebraMap K E (P.coeff 0) - c) * l 1 +
      Polynomial.C (algebraMap K E (a 0)) * l 0 +
      Polynomial.C (algebraMap K E (a 1)) * l 2 +
      Polynomial.C (algebraMap K E (a 2)) * w
  have hlinear := congrArg (aeval (![z 0 / z 1, z 2 / z 1, z 3 / z 1] : Fin 3 → G))
    (affine_polynomial_expansion P hP)
  simp [Fin.sum_univ_succ, hvalue] at hlinear
  have hlinear' : (algebraMap K G (P.coeff 0) - algebraMap E G c) * z 1 +
      algebraMap K G (a 0) * z 0 + algebraMap K G (a 1) * z 2 + algebraMap K G (a 2) * z 3 = 0 := by
    dsimp only [a]
    field_simp [hy] at hlinear
    linear_combination -hlinear
  have hl (i : Fin 3) : Polynomial.aeval t (l i) = z i.castSucc := by
    simpa [l] using (hx i).symm
  have hw' : Polynomial.aeval t w = z 3 := by
    simpa [w, show Fin.last 3 = (3 : Fin 4) by decide] using hw.symm
  have hzero : Polynomial.aeval t Q = 0 := by
    simp only [Q, map_add, map_mul, Polynomial.aeval_C, map_sub,
      ← IsScalarTower.algebraMap_apply K E G, hl, hw']
    exact hlinear'
  have hQ : Q = 0 := (transcendental_iff_injective.mp ht) (hzero.trans (map_zero _).symm)
  have hcoeff := congrArg (fun q : Polynomial E => q.coeff 2) hQ
  simp only [Q, Polynomial.coeff_add, Polynomial.coeff_C_mul] at hcoeff
  have hproduct : algebraMap K E (a 2) * C = 0 := by
    simpa [l, w] using hcoeff
  have ha : a 2 ≠ 0 := affine_polynomial_nonzero_vertex_coefficient P hP hPw
  exact (mul_ne_zero (by simpa only [map_zero] using (algebraMap K E).injective.ne ha) hC) hproduct

end DimensionFourDependence
