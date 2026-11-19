import DimensionFourDependence.ConstantVertexGaussDimension
import DimensionFourDependence.FirstOrderTaylor
import DimensionFourDependence.GenericOutputPoint

/-! # A fixed vertex line through the actual generic image point

An image line through the actual generic output value with a nonzero
constant vertex direction gives the constant normal relation. Therefore
its Gauss-image dimension is at most one. The line and its point are the
actual polynomial image equation and generic output, not auxiliary models.
-/

namespace DimensionFourDependence

open MvPolynomial

variable {K A : Type*} [Field K] [CommRing A] [Algebra K A] {n : ℕ}

/-- The linear coefficient of a polynomial restricted to an affine line
is its evaluated directional differential. -/
theorem polynomial_line_linear_coefficient (x w : Fin n → A) (P : MvPolynomial (Fin n) K) :
    (aeval (fun i => Polynomial.C (x i) + Polynomial.C (w i) * Polynomial.X) P).coeff 1 =
      evaluatedDirectionalDifferential x w P := by
  have heval (Q : MvPolynomial (Fin n) K) :
      aeval (fun i => Polynomial.C (x i)) Q = Polynomial.C (aeval x Q) :=
    (comp_aeval_apply x (Polynomial.CAlgHom (R := K) (A := A)) Q).symm
  have hdiff : evaluatedDirectionalDifferential (fun i => Polynomial.C (x i))
      (fun i => Polynomial.C (w i)) P = Polynomial.C (evaluatedDirectionalDifferential x w P) := by
    simp only [evaluatedDirectionalDifferential, heval, map_sum, map_mul]
  obtain ⟨q, hq⟩ := first_order_taylor_square_remainder (fun i => Polynomial.C (x i))
    (fun i => Polynomial.C (w i)) Polynomial.X P
  have hpoint : (fun i => Polynomial.C (x i) + Polynomial.X * Polynomial.C (w i)) =
      (fun i => Polynomial.C (x i) + Polynomial.C (w i) * Polynomial.X) := by
    funext i
    rw [mul_comm Polynomial.X]
  rw [hpoint, heval, hdiff] at hq
  have he := congrArg (fun Q : Polynomial A => Q.coeff 1) hq
  norm_num only [Polynomial.coeff_add, Polynomial.coeff_C, Polynomial.coeff_X_mul,
    Polynomial.coeff_X_pow_mul', zero_add, add_zero] at he
  simp only [ite_false, ite_true, zero_add, add_zero] at he
  exact he

variable {E : Type*} [Field E] [Algebra K E]

omit [CommRing A] [Algebra K A] in
/-- A constant-vertex line on an actual equation through the actual generic
output point forces the original polynomial image-normal relation. -/
theorem generic_vertex_line_image_normal_relation
    (H : Fin n → MvPolynomial (Fin n) K)
    [Algebra (polynomialOutputField H) E] [IsScalarTower K (polynomialOutputField H) E]
    (R : MvPolynomial (Fin n) K) (C : Fin n → K)
    (hline : aeval (fun i => Polynomial.C (genericOutputValue H E i) +
      Polynomial.C (algebraMap K E (C i)) * Polynomial.X) R = 0) :
    ∑ i, MvPolynomial.C (C i) * imageRelationNormal H R i = 0 := by
  have hd : evaluatedDirectionalDifferential (genericOutputValue H E)
      (fun i => algebraMap K E (C i)) R = 0 := by
    rw [← polynomial_line_linear_coefficient, hline]
    simp
  let D : MvPolynomial (Fin n) K := ∑ i, MvPolynomial.C (C i) * pderiv i R
  have hD : aeval (genericOutputValue H E) D = 0 := by
    calc
      _ = evaluatedDirectionalDifferential (genericOutputValue H E)
          (fun i => algebraMap K E (C i)) R := by
        simp only [D, map_sum, map_mul, aeval_C, evaluatedDirectionalDifferential]
        apply Finset.sum_congr rfl
        intro i _
        exact mul_comm _ _
      _ = 0 := hd
  have hsource := (genericOutputValue_relations H E D).mp hD
  simpa only [D, map_sum, map_mul, aeval_C, algebraMap_eq, imageRelationNormal] using hsource

variable [CharZero K]

omit [CommRing A] [Algebra K A] in
/-- A fixed nonzero vertex line through the generic image point makes the
actual Gauss-image dimension at most one, under the original map hypotheses. -/
theorem generic_vertex_line_gauss_dimension_le_one
    (H : Fin 4 → MvPolynomial (Fin 4) K)
    [Algebra (polynomialOutputField H) E] [IsScalarTower K (polynomialOutputField H) E]
    {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d)
    (hN : IsNilpotent (jac H)) (hrank : polyRank (jac H) = 3)
    (I : ImageRelationWitness H) (C : Fin 4 → K) (hC : C ≠ 0)
    (hline : aeval (fun i => Polynomial.C (genericOutputValue H E i) +
      Polynomial.C (algebraMap K E (C i)) * Polynomial.X) I.equation = 0) :
    gaussImageDimension H I ≤ 1 := by
  exact gauss_dimension_le_one_of_constant_image_normal_vertex H hd hH hN hrank I C hC
    (generic_vertex_line_image_normal_relation H I.equation C hline)

omit [CommRing A] [Algebra K A] in
/-- Gauss-image dimension two excludes a line from the actual generic image
point toward any fixed nonzero constant vertex. -/
theorem gauss_dimension_two_no_generic_vertex_line
    (H : Fin 4 → MvPolynomial (Fin 4) K)
    [Algebra (polynomialOutputField H) E] [IsScalarTower K (polynomialOutputField H) E]
    {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d)
    (hN : IsNilpotent (jac H)) (hrank : polyRank (jac H) = 3)
    (I : ImageRelationWitness H) (hGauss : gaussImageDimension H I = 2)
    (C : Fin 4 → K) (hC : C ≠ 0) :
    aeval (fun i => Polynomial.C (genericOutputValue H E i) +
      Polynomial.C (algebraMap K E (C i)) * Polynomial.X) I.equation ≠ 0 := by
  intro hline
  have hbound := generic_vertex_line_gauss_dimension_le_one H hd hH hN hrank I C hC hline
  rw [hGauss] at hbound
  norm_num at hbound

end DimensionFourDependence
