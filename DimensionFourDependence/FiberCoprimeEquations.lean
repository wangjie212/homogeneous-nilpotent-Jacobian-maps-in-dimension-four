import DimensionFourDependence.FiberCommonFactors

/-! # Removing common factors from the fiber equations

The removed factor is nonzero at the generic point. The remaining
polynomials are relatively prime, keep the degree bounds, vanish at that
point and retain independent gradients. These are the algebraic inputs
to the final geometric degree argument of Lemma 2.2.
-/

namespace DimensionFourDependence

open MvPolynomial

variable {F A : Type*} [Field F] [Field A] [Algebra F A] {n : ℕ}

/-- Remove a greatest common divisor while retaining the generic point,
degree bounds and independent gradients of two polynomial equations. -/
theorem exists_coprime_equations_at_point (x : Fin n → A) (P Q : MvPolynomial (Fin n) F)
    (hP : P ≠ 0) (hQ : Q ≠ 0) (hP0 : aeval x P = 0) (hQ0 : aeval x Q = 0)
    (hind : ∀ s t : A, s • polynomialGradientAt x P + t • polynomialGradientAt x Q = 0 →
      s = 0 ∧ t = 0) :
    ∃ r P' Q' : MvPolynomial (Fin n) F,
      P = r * P' ∧ Q = r * Q' ∧ IsRelPrime P' Q' ∧ aeval x r ≠ 0 ∧
      aeval x P' = 0 ∧ aeval x Q' = 0 ∧ P'.totalDegree ≤ P.totalDegree ∧ Q'.totalDegree ≤ Q.totalDegree ∧
      ∀ s t : A, s • polynomialGradientAt x P' + t • polynomialGradientAt x Q' = 0 → s = 0 ∧ t = 0 := by
  classical
  let : GCDMonoid (MvPolynomial (Fin n) F) := UniqueFactorizationMonoid.toGCDMonoid _
  obtain ⟨P', Q', heP, heQ, hunit⟩ := extract_gcd P Q
  let r := gcd P Q
  have hrP : r ∣ P := gcd_dvd_left P Q
  have hrQ : r ∣ Q := gcd_dvd_right P Q
  have hr : aeval x r ≠ 0 := common_factor_aeval_ne_zero x P Q r hrP hrQ hind
  have heP0 : aeval x r * aeval x P' = 0 := by rw [← map_mul, ← heP]; exact hP0
  have heQ0 : aeval x r * aeval x Q' = 0 := by rw [← map_mul, ← heQ]; exact hQ0
  have hP'0 : aeval x P' = 0 := (mul_eq_zero.mp heP0).resolve_left hr
  have hQ'0 : aeval x Q' = 0 := (mul_eq_zero.mp heQ0).resolve_left hr
  have hP'dvd : P' ∣ P := ⟨r, by rw [heP, mul_comm]⟩
  have hQ'dvd : Q' ∣ Q := ⟨r, by rw [heQ, mul_comm]⟩
  have hgP : polynomialGradientAt x P = aeval x r • polynomialGradientAt x P' := by
    rw [heP, mul_comm]
    exact polynomialGradientAt_mul_of_zero x P' r hP'0
  have hgQ : polynomialGradientAt x Q = aeval x r • polynomialGradientAt x Q' := by
    rw [heQ, mul_comm]
    exact polynomialGradientAt_mul_of_zero x Q' r hQ'0
  refine ⟨r, P', Q', heP, heQ, gcd_isUnit_iff_isRelPrime.mp hunit, hr, hP'0, hQ'0,
    totalDegree_le_of_dvd_of_isDomain hP'dvd hP, totalDegree_le_of_dvd_of_isDomain hQ'dvd hQ, ?_⟩
  intro s t hrel
  apply hind s t
  rw [hgP, hgQ]
  have hscale := congrArg (fun v => aeval x r • v) hrel
  simpa only [smul_add, smul_smul, mul_comm, smul_zero] using hscale

variable {K : Type*} [Field K] [CharZero K]

/-- Relatively prime replacements for the two equations of a fiber
witness, with the actual removed factor and all generic-point data retained. -/
theorem exists_coprime_fiber_equations
    (H : Fin 4 → FractionRing (MvPolynomial (Fin 4) K)) (W : FiberEquationWitness H) :
    ∃ r P Q : MvPolynomial (Fin 3)
        (coefficientField (K := K) (fun i : Fin 3 => H (W.chart i.castSucc))),
      W.quadric = r * P ∧ W.cubic = r * Q ∧ IsRelPrime P Q ∧
      aeval (fun i => rationalCoordinate (K := K) (W.chart i.castSucc)) r ≠ 0 ∧
      P.totalDegree ≤ 2 ∧ Q.totalDegree ≤ 3 ∧
      aeval (fun i => rationalCoordinate (K := K) (W.chart i.castSucc)) P = 0 ∧
      aeval (fun i => rationalCoordinate (K := K) (W.chart i.castSucc)) Q = 0 ∧
      ∀ s t : FractionRing (MvPolynomial (Fin 4) K),
        s • polynomialGradientAt (fun i => rationalCoordinate (K := K) (W.chart i.castSucc)) Q +
          t • polynomialGradientAt (fun i => rationalCoordinate (K := K) (W.chart i.castSucc)) P = 0 →
            s = 0 ∧ t = 0 := by
  obtain ⟨r, C', Q', hC, hQ, hcop, hr, hC0, hQ0, hCd, hQd, hind⟩ :=
    exists_coprime_equations_at_point (fun i => rationalCoordinate (K := K) (W.chart i.castSucc))
      W.cubic W.quadric (fiber_witness_cubic_ne_zero H W) (fiber_witness_quadric_ne_zero H W)
      W.cubic_zero W.quadric_zero W.gradients_independent
  exact ⟨r, Q', C', hQ, hC, hcop.symm, hr, hQd.trans W.quadric_degree,
    hCd.trans W.cubic_degree, hQ0, hC0, hind⟩

/-- A fiber equation witness after all common polynomial factors have
been removed. -/
structure CoprimeFiberEquationWitness (H : Fin 4 → FractionRing (MvPolynomial (Fin 4) K))
    extends FiberEquationWitness H where
  coprime : IsRelPrime quadric cubic

theorem exists_coprime_fiber_equation_witness
    (H : Fin 4 → FractionRing (MvPolynomial (Fin 4) K))
    (hN : IsNilpotent (rationalJacobian H)) (hrank : (rationalJacobian H).rank = 3) :
    Nonempty (CoprimeFiberEquationWitness H) := by
  obtain ⟨W⟩ := exists_fiber_equation_witness H hN hrank
  obtain ⟨_, P, Q, _, _, hcop, _, hPd, hQd, hP0, hQ0, hind⟩ := exists_coprime_fiber_equations H W
  exact ⟨{
    toFiberEquationWitness := {
      chart := W.chart
      independent := W.independent
      hyperplane := W.hyperplane
      quadric := P
      cubic := Q
      hyperplane_degree := W.hyperplane_degree
      hyperplane_last_derivative := W.hyperplane_last_derivative
      quadric_degree := hPd
      cubic_degree := hQd
      hyperplane_zero := W.hyperplane_zero
      quadric_zero := hP0
      cubic_zero := hQ0
      gradients_independent := hind }
    coprime := hcop }⟩

theorem exists_coprime_fiber_equation_witness_polynomial
    (H : Fin 4 → MvPolynomial (Fin 4) K) (hN : IsNilpotent (jac H))
    (hrank : polyRank (jac H) = 3) :
    Nonempty (CoprimeFiberEquationWitness (fun i => algebraMap (MvPolynomial (Fin 4) K)
      (FractionRing (MvPolynomial (Fin 4) K)) (H i))) := by
  let Q : Fin 4 → FractionRing (MvPolynomial (Fin 4) K) :=
    fun i => algebraMap (MvPolynomial (Fin 4) K) _ (H i)
  have hJ : rationalJacobian Q = (jac H).map
      (algebraMap (MvPolynomial (Fin 4) K) (FractionRing (MvPolynomial (Fin 4) K))) :=
    rationalJacobian_polynomial H
  apply exists_coprime_fiber_equation_witness Q
  · rw [hJ]
    exact hN.map (algebraMap (MvPolynomial (Fin 4) K)
      (FractionRing (MvPolynomial (Fin 4) K))).mapMatrix
  · rw [hJ]
    exact hrank

end DimensionFourDependence
