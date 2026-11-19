import DimensionFourDependence.FullOutputGeometricFiber

/-! # Homogeneous relations of a homogeneous polynomial map

Every homogeneous component of a relation is again a relation when the
map has positive degree. A least-degree nonzero homogeneous relation is
therefore available whenever the output coordinates are algebraically
dependent.
-/

namespace DimensionFourDependence

open MvPolynomial

variable {K σ τ : Type*} [Field K]

/-- The relation ideal of a positive-degree homogeneous map is homogeneous. -/
theorem homogeneousComponent_relation (H : σ → MvPolynomial τ K) {d : ℕ}
    (hd : 0 < d) (hH : ∀ i, (H i).IsHomogeneous d)
    (R : MvPolynomial σ K) (hR : aeval H R = 0) (k : ℕ) :
    aeval H (homogeneousComponent k R) = 0 := by
  classical
  by_cases hk : k ≤ R.totalDegree
  · have he : (∑ j ∈ Finset.range (R.totalDegree + 1),
        aeval H (homogeneousComponent j R)) = 0 := by
      rw [← map_sum, sum_homogeneousComponent, hR]
    have hc := congrArg (homogeneousComponent (d * k)) he
    simp only [map_sum, map_zero] at hc
    have hterm (j : ℕ) : homogeneousComponent (d * k)
        (aeval H (homogeneousComponent j R)) =
        if j = k then aeval H (homogeneousComponent k R) else 0 := by
      rw [homogeneousComponent_of_mem ((homogeneousComponent_isHomogeneous j R).aeval H hH)]
      by_cases hj : j = k
      · subst j
        simp
      · have hneq : d * k ≠ d * j := by
          intro heq
          exact hj (mul_left_cancel₀ (by omega : d ≠ 0) heq.symm)
        simp only [hneq, hj, ite_false]
    simp_rw [hterm] at hc
    simpa only [Finset.sum_ite_eq', Finset.mem_range.mpr (Nat.lt_succ_of_le hk), ite_true] using hc
  · rw [homogeneousComponent_eq_zero (φ := R) (n := k) (by omega), map_zero]

/-- Algebraic dependence supplies a nonzero homogeneous relation. -/
theorem exists_homogeneous_relation (H : σ → MvPolynomial τ K) {d : ℕ}
    (hd : 0 < d) (hH : ∀ i, (H i).IsHomogeneous d)
    (hdep : ¬ AlgebraicIndependent K H) :
    ∃ (R : MvPolynomial σ K) (e : ℕ), R ≠ 0 ∧ R.IsHomogeneous e ∧ aeval H R = 0 := by
  classical
  rw [algebraicIndependent_iff_injective_aeval, injective_iff_map_eq_zero] at hdep
  push Not at hdep
  obtain ⟨R, hR, hR0⟩ := hdep
  obtain ⟨e, he⟩ : ∃ e, homogeneousComponent e R ≠ 0 := by
    by_contra hn
    push Not at hn
    apply hR0
    rw [← sum_homogeneousComponent R]
    exact Finset.sum_eq_zero fun e _ => hn e
  exact ⟨_, e, he, homogeneousComponent_isHomogeneous e R,
    homogeneousComponent_relation H hd hH R hR e⟩

/-- A nonzero homogeneous relation has positive degree. -/
theorem homogeneous_relation_degree_pos (H : σ → MvPolynomial τ K)
    (R : MvPolynomial σ K) {e : ℕ} (hR0 : R ≠ 0) (hRh : R.IsHomogeneous e)
    (hR : aeval H R = 0) : 0 < e := by
  by_contra he
  have he0 : e = 0 := by omega
  have hC := eq_C_of_isHomogeneous_zero (he0 ▸ hRh)
  rw [hC] at hR
  have hc : R.coeff 0 = 0 := by simpa using hR
  exact hR0 (by rw [hC, hc, C_0])

/-- Choose a least-degree nonzero homogeneous equation of the image cone. -/
theorem exists_minimal_homogeneous_relation (H : σ → MvPolynomial τ K) {d : ℕ}
    (hd : 0 < d) (hH : ∀ i, (H i).IsHomogeneous d)
    (hdep : ¬ AlgebraicIndependent K H) :
    ∃ (R : MvPolynomial σ K) (e : ℕ),
      R ≠ 0 ∧ R.IsHomogeneous e ∧ aeval H R = 0 ∧ 0 < e ∧
      ∀ (S : MvPolynomial σ K) (f : ℕ),
        S ≠ 0 → S.IsHomogeneous f → aeval H S = 0 → e ≤ f := by
  classical
  have hex : ∃ e : ℕ, ∃ R : MvPolynomial σ K,
      R ≠ 0 ∧ R.IsHomogeneous e ∧ aeval H R = 0 := by
    obtain ⟨R, e, hR⟩ := exists_homogeneous_relation H hd hH hdep
    exact ⟨e, R, hR⟩
  obtain ⟨R, hR0, hRh, hR⟩ := Nat.find_spec hex
  refine ⟨R, Nat.find hex, hR0, hRh, hR,
    homogeneous_relation_degree_pos H R hR0 hRh hR, ?_⟩
  intro S f hS0 hSh hS
  exact Nat.find_min' hex ⟨S, hS0, hSh, hS⟩

end DimensionFourDependence
