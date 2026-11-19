import DimensionFourDependence.Defs

/-! # Source points separating a nonconstant rational polynomial ratio

Over the original infinite coefficient field, two nonproportional
polynomials have two source points where the denominator is nonzero
and the ratio has different values. This supplies the endpoints for
a source-line restriction that remains nonconstant on a Gauss curve.
-/

namespace DimensionFourDependence

open MvPolynomial

variable {K : Type*} [Field K] [Infinite K] {n : ℕ}

/-- A nonzero polynomial over the original infinite field has an
actual original-field source point where its value is nonzero. -/
theorem polynomial_exists_source_value_ne_zero
    (P : MvPolynomial (Fin n) K) (hP : P ≠ 0) :
    ∃ x : Fin n → K, MvPolynomial.eval x P ≠ 0 := by
  by_contra hn
  push Not at hn
  apply hP
  apply MvPolynomial.funext
  intro x
  simpa only [map_zero] using hn x

/-- Two nonproportional original polynomials have different ratio
values at actual original-field points where both denominators are nonzero. -/
theorem nonproportional_polynomial_ratio_separated_by_source_points
    (f g : MvPolynomial (Fin n) K) (hg : g ≠ 0)
    (hnot : ¬ ∃ c : K, f = c • g) :
    ∃ p q : Fin n → K, MvPolynomial.eval p g ≠ 0 ∧ MvPolynomial.eval q g ≠ 0 ∧
      MvPolynomial.eval p f * MvPolynomial.eval q g ≠
        MvPolynomial.eval q f * MvPolynomial.eval p g := by
  obtain ⟨p, hp⟩ := polynomial_exists_source_value_ne_zero g hg
  let c : K := MvPolynomial.eval p f / MvPolynomial.eval p g
  have hh : f - MvPolynomial.C c * g ≠ 0 := by
    intro hz
    apply hnot
    exact ⟨c, by simpa only [MvPolynomial.smul_eq_C_mul] using sub_eq_zero.mp hz⟩
  obtain ⟨q, hq⟩ := polynomial_exists_source_value_ne_zero ((f - MvPolynomial.C c * g) * g)
    (mul_ne_zero hh hg)
  have hqg : MvPolynomial.eval q g ≠ 0 := by
    intro hz
    apply hq
    rw [map_mul, hz, mul_zero]
  have hqh : MvPolynomial.eval q (f - MvPolynomial.C c * g) ≠ 0 := by
    intro hz
    apply hq
    rw [map_mul, hz, zero_mul]
  refine ⟨p, q, hp, hqg, ?_⟩
  intro he
  apply hqh
  rw [map_sub, map_mul, MvPolynomial.eval_C]
  apply sub_eq_zero.mpr
  dsimp [c]
  rw [div_mul_eq_mul_div]
  exact (eq_div_iff hp).mpr he.symm

end DimensionFourDependence
