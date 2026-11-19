import DimensionFourDependence.PlanarGroupedHomogeneousCoefficients

/-! # A pure active monomial coefficient is exactly the univariate axis coefficient -/

namespace DimensionFourDependence.Shear

open MvPolynomial

set_option maxHeartbeats 1600000

section Axis

variable {R : Type*} [CommRing R]

theorem active_first_axis_coefficient (p : MvPolynomial (Fin 2) R) (j : ℕ) :
    (aeval (![Polynomial.X, 0] : Fin 2 → Polynomial R) p).coeff j =
      p.coeff (Finsupp.single 0 j) := by
  classical
  induction p using MvPolynomial.induction_on' with
  | add p q hp hq =>
    simp only [map_add, Polynomial.coeff_add, MvPolynomial.coeff_add, hp, hq]
  | monomial e c =>
    let s : Fin 2 → Polynomial R := ![Polynomial.X, 0]
    have heq : e = Finsupp.single 0 j ↔ e 0 = j ∧ e 1 = 0 := by
      constructor
      · rintro rfl
        simp [Finsupp.single_apply]
      · rintro ⟨h0,h1⟩
        ext i
        fin_cases i <;> simp [Finsupp.single_apply, h0, h1]
    change (aeval s (monomial e c)).coeff j = (monomial e c).coeff (Finsupp.single 0 j)
    rw [aeval_monomial, Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fin.prod_univ_two,
      Polynomial.algebraMap_apply, MvPolynomial.coeff_monomial]
    change (Polynomial.C c * (Polynomial.X ^ e 0 * (0 : Polynomial R) ^ e 1)).coeff j = _
    by_cases h : e 1 = 0
    · rw [h, pow_zero, mul_one, Polynomial.C_mul_X_pow_eq_monomial, Polynomial.coeff_monomial]
      simp [h, heq, eq_comm]
    · simp [h, heq]

end Axis

variable {K : Type*} [Field K]

theorem planarCoefficientEquiv_coeff_eq_zero_of_totalDegree_lt
    (p : MvPolynomial (Fin 4) K) (m : Fin 2 →₀ ℕ) (hm : p.totalDegree < m.degree) :
    (planarCoefficientEquiv p).coeff m = 0 := by
  classical
  have hsum : planarCoefficientEquiv p =
      ∑ e ∈ p.support, monomial (activeExponents e) (monomial (baseExponents e) (p.coeff e)) := by
    conv_lhs => rw [p.as_sum, map_sum]
    apply Finset.sum_congr rfl
    intro e _
    exact planarCoefficientEquiv_monomial e (p.coeff e)
  rw [hsum, coeff_sum]
  apply Finset.sum_eq_zero
  intro e he
  have hne : activeExponents e ≠ m := by
    intro hz
    have h := activeExponents_degree_add_baseExponents_degree e
    have hle : e.degree ≤ p.totalDegree := by
      simpa only [Finsupp.degree_apply, Finsupp.sum] using le_totalDegree he
    rw [hz] at h
    omega
  simp only [coeff_monomial, if_neg hne]

end DimensionFourDependence.Shear
