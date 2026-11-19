import DimensionFourDependence.AffineConeVertexDifferential

/-! # Polynomial chain rules and constants over parameter coefficient rings

The target of the polynomial chain rule may be a commutative ring. In a
characteristic-zero domain every polynomial killed by all transverse
partials is a coefficient constant. These statements apply over K[t].
-/

namespace DimensionFourDependence

open MvPolynomial

set_option maxHeartbeats 3000000

/-- The full multivariate chain rule with a commutative target algebra,
including polynomial rings over the parameter ring. -/
theorem derivation_commutative_aeval_chain_rule
    {K R : Type*} [Field K] [CommRing R] [Algebra K R] {n : ℕ}
    (D : Derivation K R R) (x : Fin n → R) (P : MvPolynomial (Fin n) K) :
    D (aeval x P) = ∑ i, aeval x (pderiv i P) * D (x i) := by
  classical
  induction P using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq =>
    rw [map_add, map_add, hp, hq, ← Finset.sum_add_distrib]
    simp [add_mul]
  | mul_X p k hp =>
    have he : (∑ j, aeval x (pderiv j (p * X k)) * D (x j)) =
        x k * (∑ j, aeval x (pderiv j p) * D (x j)) + aeval x p * D (x k) := by
      simp only [Derivation.leibniz, pderiv_X, smul_eq_mul, map_add, map_mul, aeval_X,
        add_mul, Finset.sum_add_distrib, Finset.mul_sum]
      rw [add_comm]
      congr 1
      · exact Finset.sum_congr rfl fun j _ => by ring
      · simp [Pi.single_apply]
    rw [he, map_mul, aeval_X, D.leibniz, hp]
    simp only [smul_eq_mul]
    ring

/-- In a characteristic-zero coefficient domain, simultaneous vanishing
of all polynomial partials makes the entire polynomial a constant. -/
theorem polynomial_all_partials_zero_eq_constant
    {R : Type*} [CommRing R] [IsDomain R] [CharZero R] {n : ℕ}
    (P : MvPolynomial (Fin n) R) (hP : ∀ i, pderiv i P = 0) : P = C (P.coeff 0) := by
  classical
  ext d
  by_cases hd : d = 0
  · subst d; simp
  · obtain ⟨i, hi⟩ : ∃ i, d i ≠ 0 := by
      by_contra! hz
      apply hd
      ext i
      exact hz i
    have hle : Finsupp.single i 1 ≤ d := by
      intro j
      by_cases hj : j = i
      · subst j; simpa only [Finsupp.single_eq_same] using Nat.one_le_iff_ne_zero.mpr hi
      · simp [Finsupp.single_apply, hj]
    let m := d - Finsupp.single i 1
    have hmd : m + Finsupp.single i 1 = d := tsub_add_cancel_of_le hle
    have hc := congrArg (fun Q : MvPolynomial (Fin n) R => Q.coeff m) (hP i)
    rw [coeff_pderiv, hmd] at hc
    have hc' : P.coeff d * (↑(m i) + 1 : R) = 0 := by simpa using hc
    have hcast : (↑(m i) + 1 : R) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero (m i)
    have hcoeff : P.coeff d = 0 := (mul_eq_zero.mp hc').resolve_right hcast
    simp [coeff_C, hd, Ne.symm hd, hcoeff]

end DimensionFourDependence
