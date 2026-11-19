import DimensionFourDependence.GeometricPlanarFiber

/-! # Removing the maximal common power of a homogeneous image equation -/

namespace DimensionFourDependence

open MvPolynomial

variable {K : Type*} [Field K] {r : ℕ}

/-- A homogeneous power divisor cannot exceed the degree of a nonzero polynomial. -/
theorem homogeneous_power_dvd_degree_bound (R P : MvPolynomial (Fin r) K) {n : ℕ}
    (hR0 : R ≠ 0) (hRh : R.IsHomogeneous n) (hP : P ≠ 0) (m : ℕ) (hm : R ^ m ∣ P) :
    n * m ≤ P.totalDegree := by
  obtain ⟨Q, hQ⟩ := hm
  have hQ0 : Q ≠ 0 := by
    intro hz
    apply hP
    rw [hQ, hz, mul_zero]
  have he := congrArg MvPolynomial.totalDegree hQ
  rw [totalDegree_mul_of_isDomain (pow_ne_zero m hR0) hQ0,
    (hRh.pow m).totalDegree (pow_ne_zero m hR0)] at he
  omega

/-- A nonzero polynomial vector has a maximal common power of every
nonzero positive-degree homogeneous polynomial. -/
theorem exists_saturated_common_power
    (R : MvPolynomial (Fin r) K) {n : ℕ} (hn : 0 < n) (hR0 : R ≠ 0) (hRh : R.IsHomogeneous n)
    (H : Fin r → MvPolynomial (Fin r) K) (hH0 : H ≠ 0) :
    ∃ (m : ℕ) (V : Fin r → MvPolynomial (Fin r) K),
      H = (fun i => R ^ m * V i) ∧ ∃ j, ¬ R ∣ V j := by
  classical
  obtain ⟨i, hi⟩ : ∃ i, H i ≠ 0 := by
    simpa only [ne_eq, funext_iff, Pi.zero_apply, not_forall] using hH0
  have hex : ∃ k : ℕ, ¬ ∀ j, R ^ k ∣ H j := by
    refine ⟨(H i).totalDegree + 1, ?_⟩
    intro hh
    have hb := homogeneous_power_dvd_degree_bound R (H i) hR0 hRh hi _ (hh i)
    have hlow : (H i).totalDegree + 1 ≤ n * ((H i).totalDegree + 1) := by
      simpa only [one_mul] using Nat.mul_le_mul_right ((H i).totalDegree + 1) (show 1 ≤ n by omega)
    omega
  let k := Nat.find hex
  have hkpos : 0 < k := by
    by_contra hn
    have hk0 : k = 0 := by omega
    have hh := Nat.find_spec hex
    change ¬ ∀ j, R ^ k ∣ H j at hh
    rw [hk0] at hh
    simp at hh
  let m := k - 1
  have hprev : ∀ j, R ^ m ∣ H j := by
    by_contra hh
    exact Nat.find_min hex (by change k - 1 < k; omega) hh
  choose V hV using hprev
  have hnext : ∃ j, ¬ R ^ (m + 1) ∣ H j := by
    have hh := Nat.find_spec hex
    change ¬ ∀ j, R ^ k ∣ H j at hh
    rw [show k = m + 1 by dsimp [m]; omega] at hh
    push Not at hh
    exact hh
  obtain ⟨j, hj⟩ := hnext
  refine ⟨m, V, funext hV, j, ?_⟩
  rintro ⟨Q, hQ⟩
  apply hj
  refine ⟨Q, ?_⟩
  rw [hV j, hQ, pow_succ]
  ring

/-- Dividing a homogeneous common factor leaves a homogeneous vector of
the corresponding degree difference, including its zero components. -/
theorem homogeneous_vector_remove_power
    (R : MvPolynomial (Fin r) K) {n d : ℕ} (hR0 : R ≠ 0) (hRh : R.IsHomogeneous n)
    (H V : Fin r → MvPolynomial (Fin r) K) (hH : IsHomogMap H d) (m : ℕ)
    (hHV : H = fun i => R ^ m * V i) : IsHomogMap V (d - n * m) := by
  intro i
  by_cases hVi : V i = 0
  · rw [hVi]
    exact isHomogeneous_zero _ _ _
  have hprod : (R ^ m * V i).IsHomogeneous d := by
    rw [← congrFun hHV i]
    exact hH i
  obtain ⟨e, he⟩ := isHomogeneous_of_mul_left
    (p := V i) (q := R ^ m) (by simpa only [mul_comm] using hprod)
    (mul_ne_zero hVi (pow_ne_zero m hR0))
  have hdeg : n * m + e = d :=
    ((hRh.pow m).mul he).inj_right hprod (mul_ne_zero (pow_ne_zero m hR0) hVi)
  have heq : d - n * m = e := by omega
  rw [heq]
  exact he

end DimensionFourDependence
