import DimensionFourDependence.HomogeneousAffineReflection
import DimensionFourDependence.FirstOrderTaylor

/-! # The next highest affine coefficient is the tangent form

First-order Taylor expansion gives the coefficient of the line parameter
at degree one. Reflection of a homogeneous affine substitution places the
same differential at its original degree minus one. Vanishing at the
direction removes the top coefficient, with no genericity assumption.
-/

namespace DimensionFourDependence

open MvPolynomial

set_option maxHeartbeats 2000000

variable {K E : Type*} [Field K] [Field E] [Algebra K E] {n : ℕ}

/-- The linear coefficient of any affine-line substitution is its
actual evaluated directional differential at the base point. -/
theorem affine_line_coefficient_one
    (P : MvPolynomial (Fin n) K) (x A : Fin n → E) :
    (aeval (fun i => Polynomial.C (x i) + Polynomial.C (A i) * Polynomial.X) P).coeff 1 =
      ∑ i, aeval x (pderiv i P) * A i := by
  classical
  have hC (Q : MvPolynomial (Fin n) K) :
      aeval (fun i => Polynomial.C (x i)) Q = Polynomial.C (aeval x Q) := by
    exact (comp_aeval_apply x (IsScalarTower.toAlgHom K E (Polynomial E)) Q).symm
  obtain ⟨q, hq⟩ := first_order_taylor_square_remainder
    (fun i => Polynomial.C (x i)) (fun i => Polynomial.C (A i)) Polynomial.X P
  have hpoint : (fun i : Fin n => Polynomial.C (x i) + Polynomial.X * Polynomial.C (A i)) =
      (fun i => Polynomial.C (x i) + Polynomial.C (A i) * Polynomial.X) := by
    funext i
    ring
  rw [hpoint] at hq
  have hdiff : evaluatedDirectionalDifferential (fun i => Polynomial.C (x i))
      (fun i => Polynomial.C (A i)) P = Polynomial.C (∑ i, aeval x (pderiv i P) * A i) := by
    simp only [evaluatedDirectionalDifferential, hC, map_sum, map_mul]
  rw [hC, hdiff] at hq
  have he := congrArg (fun p : Polynomial E => p.coeff 1) hq
  simpa only [Polynomial.coeff_add, Polynomial.coeff_X_mul, Polynomial.coeff_C,
    Polynomial.coeff_X_pow_mul', show ¬ (2 : ℕ) ≤ 1 from by decide,
    show (1 : ℕ) ≠ 0 from by decide, ite_false, ite_true, zero_add, add_zero] using he

/-- At a positive homogeneous degree, the next highest coefficient is
the tangent differential at the direction applied to the base point. -/
theorem homogeneous_affine_line_tangent_coefficient
    (P : MvPolynomial (Fin n) K) {D : ℕ} (hD : 0 < D)
    (hP : P.IsHomogeneous D) (x A : Fin n → E) :
    (aeval (fun i => Polynomial.C (x i) + Polynomial.C (A i) * Polynomial.X) P).coeff (D - 1) =
      ∑ i, aeval A (pderiv i P) * x i := by
  have he := congrArg (fun p : Polynomial E => p.coeff 1)
    (homogeneous_affine_line_reflection P hP x A)
  rw [Polynomial.coeff_reflect, Polynomial.revAt_le (by omega : 1 ≤ D)] at he
  exact he.trans (affine_line_coefficient_one P A x)

/-- Vanishing at the direction removes the original top degree. -/
theorem homogeneous_affine_line_degree_drop
    (P : MvPolynomial (Fin n) K) {D : ℕ} (hP : P.IsHomogeneous D)
    (x A : Fin n → E) (hzero : aeval A P = 0) :
    (aeval (fun i => Polynomial.C (x i) + Polynomial.C (A i) * Polynomial.X) P).natDegree ≤ D - 1 := by
  let s : Fin n → Polynomial E := fun i => Polynomial.C (x i) + Polynomial.C (A i) * Polynomial.X
  have hs (i : Fin n) : (s i).natDegree ≤ 1 := by
    apply Polynomial.natDegree_add_le_of_degree_le (by simp)
    exact Polynomial.natDegree_mul_le.trans (by simpa using (Polynomial.natDegree_X_le (R := E)))
  have heval : (aeval s P).natDegree ≤ P.totalDegree :=
    polynomial_natDegree_aeval_le_totalDegree s hs P
  have hbound : (aeval s P).natDegree ≤ D := heval.trans hP.totalDegree_le
  have hcoeff : (aeval s P).coeff D = 0 := by
    rw [homogeneous_affine_line_coefficient_at_degree P hP x A, hzero]
  exact Polynomial.natDegree_le_pred hbound hcoeff

end DimensionFourDependence
