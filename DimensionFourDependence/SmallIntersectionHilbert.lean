import DimensionFourDependence.HomogeneousIntersection

/-! # Linear Hilbert growth for the quadratic-cubic intersection

The identity is evaluated for all possible positive equation degrees at
most two and three. Monotonicity then bounds the actual fiber's Hilbert
function. Identifying a geometric degree still requires its Hilbert polynomial.
-/

namespace DimensionFourDependence

open MvPolynomial Module

variable {L : Type*} [Field L]

/-- The complete-intersection Hilbert function is explicitly linear in
all positive degree cases up to two and three. -/
theorem small_completeIntersection_hilbert_twice
    (p q : MvPolynomial (Option (Fin 3)) L) {dp dq : ℕ}
    (hp : p.IsHomogeneous dp) (hq : q.IsHomogeneous dq) (hp0 : p ≠ 0) (hcop : IsRelPrime p q)
    (hdp0 : 0 < dp) (hdp : dp ≤ 2) (hdq0 : 0 < dq) (hdq : dq ≤ 3) (m : ℕ) :
    2 * projectiveHilbertFunction (Ideal.span ({p, q} : Set (MvPolynomial (Option (Fin 3)) L)))
      (dp + dq + m) = dp * dq * (2 * m + dp + dq + 4) := by
  have hi := completeIntersection_hilbert_identity p q hp hq hp0 hcop m
  simp only [homogeneousPiece_four_finrank] at hi
  interval_cases dp <;> interval_cases dq <;>
    norm_num [Nat.add_choose_eq, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
      Finset.sum_range_succ] at hi ⊢ <;>
    norm_num [Nat.choose_succ_succ] at hi ⊢ <;> omega

/-- The Hilbert function of the complete intersection has eventual
linear growth with coefficient at most six. -/
theorem small_completeIntersection_hilbert_le_six
    (p q : MvPolynomial (Option (Fin 3)) L) {dp dq : ℕ}
    (hp : p.IsHomogeneous dp) (hq : q.IsHomogeneous dq) (hp0 : p ≠ 0) (hcop : IsRelPrime p q)
    (hdp0 : 0 < dp) (hdp : dp ≤ 2) (hdq0 : 0 < dq) (hdq : dq ≤ 3)
    (n : ℕ) (hn : dp + dq ≤ n) :
    projectiveHilbertFunction (Ideal.span ({p, q} : Set (MvPolynomial (Option (Fin 3)) L))) n ≤
      6 * (n + 1) := by
  have hN : dp + dq + (n - (dp + dq)) = n := Nat.add_sub_of_le hn
  have he := small_completeIntersection_hilbert_twice p q hp hq hp0 hcop hdp0 hdp hdq0 hdq
    (n - (dp + dq))
  rw [hN] at he
  interval_cases dp <;> interval_cases dq <;> norm_num at he ⊢ <;> omega

variable {K : Type*} [Field K] [CharZero K]

omit [CharZero K] in
/-- The actual homogeneous closure prime has Hilbert function at most
`6(n+1)` in every degree at least five. -/
theorem projective_fiber_witness_hilbert_le_six
    (H : Fin 4 → FractionRing (MvPolynomial (Fin 4) K)) (W : ProjectiveFiberEquationWitness H)
    (n : ℕ) (hn : 5 ≤ n) :
    projectiveHilbertFunction (projectiveConeIdeal
      (L := coefficientField (K := K) (fun i : Fin 3 => H (W.affine.chart i.castSucc)))
      (fun i : Fin 3 => rationalCoordinate (K := K) (W.affine.chart i.castSucc))) n ≤ 6 * (n + 1) := by
  have hm := projective_fiber_witness_equations_mem_prime H W
  have hs : Ideal.span ({W.quadric, W.cubic} : Set (MvPolynomial (Option (Fin 3))
      (coefficientField (K := K) (fun i : Fin 3 => H (W.affine.chart i.castSucc))))) ≤
      projectiveConeIdeal
        (L := coefficientField (K := K) (fun i : Fin 3 => H (W.affine.chart i.castSucc)))
        (fun i : Fin 3 => rationalCoordinate (K := K) (W.affine.chart i.castSucc)) := by
    apply Ideal.span_le.mpr
    intro z hz
    rcases hz with rfl | rfl
    · exact hm.1
    · exact hm.2
  apply (projectiveHilbertFunction_antitone hs n).trans
  apply small_completeIntersection_hilbert_le_six W.quadric W.cubic
    W.quadric_homogeneous W.cubic_homogeneous W.quadric_ne_zero W.coprime
    W.quadric_degree_pos W.affine.quadric_degree W.cubic_degree_pos W.affine.cubic_degree n
  exact (Nat.add_le_add W.affine.quadric_degree W.affine.cubic_degree).trans hn

end DimensionFourDependence
