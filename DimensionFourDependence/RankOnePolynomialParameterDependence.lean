import DimensionFourDependence.PolynomialParameterTraceSpecialization
import DimensionFourDependence.PlanarNilpotentDependence

/-! # A one-parameter polynomial map of zero trace has dependent outputs -/

namespace DimensionFourDependence

open MvPolynomial Matrix

set_option maxHeartbeats 1250000

variable {K : Type*} [Field K] [CharZero K] {n : ℕ}
local notation "R₀" => MvPolynomial (Fin n) K

/-- A normalized map whose outputs are polynomials in one common
parameter has a constant component relation as soon as its trace vanishes. -/
theorem normalized_polynomial_parameter_map_trace_zero_componentsDependent
    (H : Fin n → R₀) (h0 : ∀ i, aeval (fun _ : Fin n => (0 : K)) (H i) = 0)
    (r : R₀) (hr : 0 < r.totalDegree)
    (A : Fin n → Polynomial K) (hA : ∀ i, H i = Polynomial.aeval r (A i))
    (htrace : Matrix.trace (jac H) = 0) : ComponentsDependent H := by
  have htrace' : ∑ i, Polynomial.aeval r (A i).derivative * pderiv i r = 0 := by
    have hp (i : Fin n) : pderiv i (H i) = Polynomial.aeval r (A i).derivative * pderiv i r := by
      rw [hA]
      simpa only [smul_eq_mul, mul_comm] using (pderiv (R := K) i).map_aeval (A i) r
    simpa only [Matrix.trace, Matrix.diag, jac, Matrix.of_apply, hp] using htrace
  have hrp : ∃ i, pderiv i r ≠ 0 := by
    by_contra h
    push Not at h
    have heq := polynomial_all_partials_zero_eq_constant r h
    have hdegree := congrArg totalDegree heq
    rw [totalDegree_C] at hdegree
    omega
  obtain ⟨j, hj⟩ := hrp
  classical
  obtain ⟨m, hm⟩ := support_nonempty.mpr hj
  have hm0 := mem_support_iff.mp hm
  let c : Fin n → K := fun i => (pderiv i r).coeff m
  have hc : c ≠ 0 := by
    intro hz
    exact hm0 (congrFun hz j)
  let P : Polynomial K := ∑ i, Polynomial.C (c i) * A i
  have hder : P.derivative = 0 := by
    apply Polynomial.eq_zero_of_infinite_isRoot
    apply Set.infinite_univ.mono
    intro t _
    have hspec := polynomial_parameter_trace_specializes_globally r hr
      (fun i => (A i).derivative) htrace' t
    have hcoeff := congrArg (fun Q : R₀ => Q.coeff m) hspec
    change (∑ i, C ((A i).derivative.eval t) * pderiv i r : R₀).coeff m =
      (0 : R₀).coeff m at hcoeff
    rw [MvPolynomial.coeff_sum] at hcoeff
    simp only [coeff_C_mul, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply] at hcoeff
    change P.derivative.eval t = 0
    simp only [P, Polynomial.derivative_sum, Polynomial.derivative_C_mul,
      Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C]
    simpa only [c, mul_comm] using hcoeff
  have hP := Polynomial.eq_C_of_natDegree_eq_zero (Polynomial.derivative_eq_zero.mp hder)
  have heval : ∑ i, c i • H i = C (P.coeff 0) := by
    have he := congrArg (Polynomial.aeval r) hP
    change Polynomial.aeval r (∑ i, Polynomial.C (c i) * A i) =
      Polynomial.aeval r (Polynomial.C (P.coeff 0)) at he
    simpa only [map_sum, map_mul, Polynomial.aeval_C, algebraMap_eq, smul_eq_C_mul, ← hA] using he
  have hs : P.coeff 0 = 0 := by
    have he := congrArg (aeval (fun _ : Fin n => (0 : K))) heval
    change aeval (fun _ : Fin n => (0 : K)) (∑ i, c i • H i) =
      aeval (fun _ : Fin n => (0 : K)) (C (P.coeff 0) : R₀) at he
    simpa only [map_sum, smul_eq_C_mul, map_mul, aeval_C, h0, mul_zero, Finset.sum_const_zero,
      Algebra.algebraMap_self_apply] using he.symm
  exact ⟨c, hc, by rw [heval, hs, map_zero]⟩

end DimensionFourDependence
