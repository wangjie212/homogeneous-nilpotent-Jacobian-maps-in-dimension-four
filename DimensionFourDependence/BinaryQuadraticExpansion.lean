import DimensionFourDependence.AffineTwoCoordinateLine

/-! # The six actual coefficients of a binary polynomial of degree at most two

This expansion retains the original constant, linear, square and mixed
coefficients. It will detect the cubic and quartic terms introduced by
the actual quadratic shear of a projected relation.
-/

namespace DimensionFourDependence

open MvPolynomial

variable {L : Type*} [Field L]

/-- A binary monomial of total degree at most two has one of the
six specified original exponent vectors. -/
theorem binary_exponent_degree_le_two (m : Option Unit →₀ ℕ) (hm : m.degree ≤ 2) :
    m = 0 ∨ m = Finsupp.single none 1 ∨ m = Finsupp.single (some ()) 1 ∨
      m = Finsupp.single none 2 ∨ m = Finsupp.single none 1 + Finsupp.single (some ()) 1 ∨
      m = Finsupp.single (some ()) 2 := by
  have hsum : m none + m (some ()) ≤ 2 := by
    simpa [Finsupp.degree_eq_sum, Fintype.sum_option] using hm
  have hsplit : m = Finsupp.single none (m none) + Finsupp.single (some ()) (m (some ())) := by
    ext j
    cases j with
    | none => simp
    | some u => cases u; simp
  generalize ha : m none = a at *
  generalize hb : m (some ()) = b at *
  have haBound : a ≤ 2 := by omega
  have hbBound : b ≤ 2 := by omega
  interval_cases a <;> interval_cases b <;> simp_all

/-- The entire binary quadratic is the sum of its actual six
monomial coefficients, with no chosen coefficient presentation. -/
theorem binary_quadratic_monomial_expansion
    (P : MvPolynomial (Option Unit) L) (hP : P.totalDegree ≤ 2) :
    P = monomial 0 (P.coeff 0) +
      monomial (Finsupp.single none 1) (P.coeff (Finsupp.single none 1)) +
      monomial (Finsupp.single (some ()) 1) (P.coeff (Finsupp.single (some ()) 1)) +
      monomial (Finsupp.single none 2) (P.coeff (Finsupp.single none 2)) +
      monomial (Finsupp.single none 1 + Finsupp.single (some ()) 1)
        (P.coeff (Finsupp.single none 1 + Finsupp.single (some ()) 1)) +
      monomial (Finsupp.single (some ()) 2) (P.coeff (Finsupp.single (some ()) 2)) := by
  classical
  ext m
  by_cases hm : m.degree ≤ 2
  · rcases binary_exponent_degree_le_two m hm with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [coeff_monomial, Finsupp.ext_iff, Option.forall]
  · have hc : P.coeff m = 0 := by
      by_contra hne
      exact hm ((le_totalDegree (mem_support_iff.mpr hne)).trans hP)
    have hneq : m ≠ 0 ∧ m ≠ Finsupp.single none 1 ∧ m ≠ Finsupp.single (some ()) 1 ∧
        m ≠ Finsupp.single none 2 ∧ m ≠ Finsupp.single none 1 + Finsupp.single (some ()) 1 ∧
        m ≠ Finsupp.single (some ()) 2 := by
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intro he <;> subst m <;>
        norm_num [Finsupp.degree_eq_sum, Fintype.sum_option] at hm
    simp [coeff_monomial, hc, hneq.1, hneq.2.1, hneq.2.2.1,
      hneq.2.2.2.1, hneq.2.2.2.2.1, hneq.2.2.2.2.2, eq_comm]

/-- The same expansion in the actual coordinate powers Y and T. -/
theorem binary_quadratic_coordinate_expansion
    (P : MvPolynomial (Option Unit) L) (hP : P.totalDegree ≤ 2) :
    ∃ a b c d e f : L,
      P = C a + C b * X none + C c * X (some ()) + C d * X none ^ 2 +
        C e * X none * X (some ()) + C f * X (some ()) ^ 2 := by
  refine ⟨P.coeff 0, P.coeff (Finsupp.single none 1), P.coeff (Finsupp.single (some ()) 1),
    P.coeff (Finsupp.single none 2),
    P.coeff (Finsupp.single none 1 + Finsupp.single (some ()) 1),
    P.coeff (Finsupp.single (some ()) 2), ?_⟩
  calc
    P = _ := binary_quadratic_monomial_expansion P hP
    _ = _ := by
      simp only [← C_apply, ← C_mul_X_pow_eq_monomial, pow_one, monomial_add_single]

end DimensionFourDependence
