import DimensionFourDependence.FiberCoprimeEquations
import DimensionFourDependence.HomogenizeChart
import DimensionFourDependence.HomogenizeCoprime

/-! # Homogeneous projective equations for the generic fiber

The equations are homogenized to their actual degrees after common factors
have been removed. The affine chart, relative primality, degree bounds and
gradient independence are all preserved. The degree of the fiber curve itself
still requires the separate geometric intersection argument.
-/

namespace DimensionFourDependence

open MvPolynomial

/-- A nonzero polynomial vanishing at a field-valued point is nonconstant. -/
theorem totalDegree_pos_of_aeval_zero {R A σ : Type*} [Field R] [Field A] [Algebra R A]
    (x : σ → A) (p : MvPolynomial σ R) (hp : p ≠ 0) (hzero : aeval x p = 0) :
    0 < p.totalDegree := by
  by_contra h
  have hd : p.totalDegree = 0 := by omega
  have he := totalDegree_eq_zero_iff_eq_C.mp hd
  rw [he] at hzero
  simp only [aeval_C] at hzero
  have hc : p.coeff 0 = 0 := (algebraMap R A).injective (by simpa only [map_zero] using hzero)
  apply hp
  rw [he, hc, map_zero]

variable {K : Type*} [Field K] [CharZero K]

/-- The actual generic source point in the affine chart of projective space. -/
noncomputable def fiberProjectivePoint (p : Equiv.Perm (Fin 4)) :
    Option (Fin 3) → FractionRing (MvPolynomial (Fin 4) K) :=
  fun j => j.elim 1 (fun i => rationalCoordinate (K := K) (p i.castSucc))

theorem fiberProjectivePoint_ne_zero (p : Equiv.Perm (Fin 4)) :
    fiberProjectivePoint (K := K) p ≠ 0 := by
  intro h
  have hi := congrFun h none
  change (1 : FractionRing (MvPolynomial (Fin 4) K)) = 0 at hi
  exact one_ne_zero hi

/-- Homogeneous equations over the actual coefficient field, with the
affine source equations and every homogenization property retained. -/
structure ProjectiveFiberEquationWitness
    (H : Fin 4 → FractionRing (MvPolynomial (Fin 4) K)) where
  affine : CoprimeFiberEquationWitness H
  quadric : MvPolynomial (Option (Fin 3))
    (coefficientField (K := K) (fun i : Fin 3 => H (affine.chart i.castSucc)))
  cubic : MvPolynomial (Option (Fin 3))
    (coefficientField (K := K) (fun i : Fin 3 => H (affine.chart i.castSucc)))
  quadric_homogeneous : quadric.IsHomogeneous affine.quadric.totalDegree
  cubic_homogeneous : cubic.IsHomogeneous affine.cubic.totalDegree
  quadric_degree : quadric.totalDegree = affine.quadric.totalDegree
  cubic_degree : cubic.totalDegree = affine.cubic.totalDegree
  quadric_degree_pos : 0 < affine.quadric.totalDegree
  cubic_degree_pos : 0 < affine.cubic.totalDegree
  quadric_ne_zero : quadric ≠ 0
  cubic_ne_zero : cubic ≠ 0
  quadric_affine : projectiveDehomogenize quadric = affine.quadric
  cubic_affine : projectiveDehomogenize cubic = affine.cubic
  coprime : IsRelPrime quadric cubic
  quadric_no_infinity_factor : ¬ X none ∣ quadric
  cubic_no_infinity_factor : ¬ X none ∣ cubic
  quadric_zero : aeval (fiberProjectivePoint (K := K) affine.chart) quadric = 0
  cubic_zero : aeval (fiberProjectivePoint (K := K) affine.chart) cubic = 0
  gradients_independent : ∀ s t : FractionRing (MvPolynomial (Fin 4) K),
    s • (fun i : Fin 3 => aeval (fiberProjectivePoint (K := K) affine.chart) (pderiv (some i) cubic)) +
      t • (fun i : Fin 3 => aeval (fiberProjectivePoint (K := K) affine.chart) (pderiv (some i) quadric)) = 0 →
        s = 0 ∧ t = 0

omit [CharZero K] in
/-- The equation-degree product is at most six. This is the numerical
input to Bézout, not yet a statement about the degree of a curve. -/
theorem projective_fiber_equation_degree_product_le_six
    (H : Fin 4 → FractionRing (MvPolynomial (Fin 4) K)) (W : ProjectiveFiberEquationWitness H) :
    W.quadric.totalDegree * W.cubic.totalDegree ≤ 6 := by
  rw [W.quadric_degree, W.cubic_degree]
  exact (Nat.mul_le_mul W.affine.quadric_degree W.affine.cubic_degree).trans (by norm_num)

/-- The complete actual-degree homogenization data follow from the
nilpotent rank-three rational-map hypotheses. -/
theorem exists_projective_fiber_equation_witness
    (H : Fin 4 → FractionRing (MvPolynomial (Fin 4) K))
    (hN : IsNilpotent (rationalJacobian H)) (hrank : (rationalJacobian H).rank = 3) :
    Nonempty (ProjectiveFiberEquationWitness H) := by
  obtain ⟨W⟩ := exists_coprime_fiber_equation_witness H hN hrank
  have hp := fiber_witness_quadric_ne_zero H W.toFiberEquationWitness
  have hq := fiber_witness_cubic_ne_zero H W.toFiberEquationWitness
  let P := projectiveHomogenize W.quadric W.quadric.totalDegree
  let Q := projectiveHomogenize W.cubic W.cubic.totalDegree
  have hA (i : Fin 3) : aeval (fiberProjectivePoint (K := K) W.chart) (pderiv (some i) Q) =
      aeval (fun j => rationalCoordinate (K := K) (W.chart j.castSucc)) (pderiv i W.cubic) :=
    projectiveHomogenize_gradient_aeval_chart W.cubic W.cubic.totalDegree _ i
  have hB (i : Fin 3) : aeval (fiberProjectivePoint (K := K) W.chart) (pderiv (some i) P) =
      aeval (fun j => rationalCoordinate (K := K) (W.chart j.castSucc)) (pderiv i W.quadric) :=
    projectiveHomogenize_gradient_aeval_chart W.quadric W.quadric.totalDegree _ i
  refine ⟨{
    affine := W
    quadric := P
    cubic := Q
    quadric_homogeneous := projectiveHomogenize_isHomogeneous W.quadric _ le_rfl
    cubic_homogeneous := projectiveHomogenize_isHomogeneous W.cubic _ le_rfl
    quadric_degree := projectiveHomogenize_totalDegree hp _ le_rfl
    cubic_degree := projectiveHomogenize_totalDegree hq _ le_rfl
    quadric_degree_pos := totalDegree_pos_of_aeval_zero _ W.quadric hp W.quadric_zero
    cubic_degree_pos := totalDegree_pos_of_aeval_zero _ W.cubic hq W.cubic_zero
    quadric_ne_zero := projectiveHomogenize_ne_zero hp _
    cubic_ne_zero := projectiveHomogenize_ne_zero hq _
    quadric_affine := projectiveDehomogenize_homogenize W.quadric _
    cubic_affine := projectiveDehomogenize_homogenize W.cubic _
    coprime := projectiveHomogenize_isRelPrime hp W.coprime
    quadric_no_infinity_factor := X_none_not_dvd_projectiveHomogenize hp
    cubic_no_infinity_factor := X_none_not_dvd_projectiveHomogenize hq
    quadric_zero := ?_
    cubic_zero := ?_
    gradients_independent := ?_ }⟩
  · exact (projectiveHomogenize_aeval_chart W.quadric W.quadric.totalDegree
      (fun i => rationalCoordinate (K := K) (W.chart i.castSucc))).trans W.quadric_zero
  · exact (projectiveHomogenize_aeval_chart W.cubic W.cubic.totalDegree
      (fun i => rationalCoordinate (K := K) (W.chart i.castSucc))).trans W.cubic_zero
  · intro s t hrel
    apply W.gradients_independent s t
    simpa only [hA, hB] using hrel

theorem exists_projective_fiber_equation_witness_polynomial
    (H : Fin 4 → MvPolynomial (Fin 4) K) (hN : IsNilpotent (jac H))
    (hrank : polyRank (jac H) = 3) :
    Nonempty (ProjectiveFiberEquationWitness (fun i => algebraMap (MvPolynomial (Fin 4) K)
      (FractionRing (MvPolynomial (Fin 4) K)) (H i))) := by
  let Q : Fin 4 → FractionRing (MvPolynomial (Fin 4) K) :=
    fun i => algebraMap (MvPolynomial (Fin 4) K) _ (H i)
  have hJ : rationalJacobian Q = (jac H).map
      (algebraMap (MvPolynomial (Fin 4) K) (FractionRing (MvPolynomial (Fin 4) K))) :=
    rationalJacobian_polynomial H
  apply exists_projective_fiber_equation_witness Q
  · rw [hJ]
    exact hN.map (algebraMap (MvPolynomial (Fin 4) K)
      (FractionRing (MvPolynomial (Fin 4) K))).mapMatrix
  · rw [hJ]
    exact hrank

end DimensionFourDependence
