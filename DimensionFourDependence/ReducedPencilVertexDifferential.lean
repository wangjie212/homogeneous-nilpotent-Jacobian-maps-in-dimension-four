import DimensionFourDependence.Homogeneous

/-! # A reduced vertex-dependent homogeneous pencil has a nonzero vertex differential

In characteristic zero a zero partial derivative removes that variable
from every supported monomial. Coprimality then rules out cancellation
in the vertex Wronskian of a homogeneous reduced parameter quotient.
This supplies the nonconstant-parameter input for source independence.
-/

namespace DimensionFourDependence

open MvPolynomial

variable {K σ : Type*} [Field K] [CharZero K]

/-- A zero partial derivative in characteristic zero forces actual
degree zero in that variable, with no homogeneity assumption. -/
theorem degreeOf_eq_zero_of_pderiv_eq_zero
    (P : MvPolynomial σ K) (i : σ) (hder : pderiv i P = 0) : P.degreeOf i = 0 := by
  classical
  rw [degreeOf_eq_sup]
  apply Finset.sup_eq_zero.mpr
  intro d hd
  by_contra hdi
  have hpos : 1 ≤ d i := by omega
  have hle : Finsupp.single i 1 ≤ d := by
    intro j
    by_cases hj : j = i
    · subst j
      simpa only [Finsupp.single_eq_same] using hpos
    · simp [Finsupp.single_apply, hj]
  let m : σ →₀ ℕ := d - Finsupp.single i 1
  have hmd : m + Finsupp.single i 1 = d := tsub_add_cancel_of_le hle
  have hc := congrArg (fun Q : MvPolynomial σ K => Q.coeff m) hder
  rw [coeff_pderiv, hmd] at hc
  have hc' : P.coeff d * (↑(m i) + 1 : K) = 0 := by simpa using hc
  have hcast : (↑(m i) + 1 : K) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero (m i)
  exact (mem_support_iff.mp hd) ((mul_eq_zero.mp hc').resolve_right hcast)

/-- Vanishing of one vertex Wronskian for a reduced homogeneous
pencil forces both original members to have zero vertex degree. -/
theorem reduced_homogeneous_pencil_zero_wronskian_vertex_degrees [Fintype σ]
    (p q : MvPolynomial σ K) (hp0 : p ≠ 0) (hrel : IsRelPrime p q)
    {d e : ℕ} (hp : p.IsHomogeneous d) (hq : q.IsHomogeneous e) (i : σ)
    (hzero : q * pderiv i p - p * pderiv i q = 0) :
    p.degreeOf i = 0 ∧ q.degreeOf i = 0 := by
  have hcross : q * pderiv i p = p * pderiv i q := sub_eq_zero.mp hzero
  have hpdiv : p ∣ pderiv i p := hrel.dvd_of_dvd_mul_left ⟨pderiv i q, hcross⟩
  have hpder : pderiv i p = 0 := pderiv_eq_zero_of_dvd hp i hpdiv
  have hqder : pderiv i q = 0 := by
    have he : p * pderiv i q = 0 := by rw [← hcross, hpder, mul_zero]
    exact (mul_eq_zero.mp he).resolve_left hp0
  exact ⟨degreeOf_eq_zero_of_pderiv_eq_zero p i hpder,
    degreeOf_eq_zero_of_pderiv_eq_zero q i hqder⟩

/-- Either actual positive vertex degree makes the original reduced
parameter quotient's vertex Wronskian nonzero. -/
theorem reduced_homogeneous_vertex_dependent_pencil_wronskian_ne_zero [Fintype σ]
    (p q : MvPolynomial σ K) (hp0 : p ≠ 0) (hrel : IsRelPrime p q)
    {d e : ℕ} (hp : p.IsHomogeneous d) (hq : q.IsHomogeneous e) (i : σ)
    (hvertex : 0 < p.degreeOf i ∨ 0 < q.degreeOf i) :
    q * pderiv i p - p * pderiv i q ≠ 0 := by
  intro hz
  obtain ⟨hpdeg, hqdeg⟩ := reduced_homogeneous_pencil_zero_wronskian_vertex_degrees
    p q hp0 hrel hp hq i hz
  rcases hvertex with h | h <;> omega

end DimensionFourDependence
