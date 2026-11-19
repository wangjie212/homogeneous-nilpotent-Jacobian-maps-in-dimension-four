import DimensionFourDependence.ValuationProjectiveHilbertSpecialization

/-! # A smaller growing homogeneous Hilbert function constructs its own positive curve degree -/

namespace DimensionFourDependence

open Polynomial

attribute [local instance] MvPolynomial.gradedAlgebra

set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 100000

variable {K L σ τ : Type*} [Field K] [Field L] [Finite σ]

/-- A homogeneous coordinate ideal with at least linear growth and
Hilbert function bounded by an actual curve constructs a positive
integral curve degree bounded by that curve's degree. No degree or
Hilbert-polynomial linearity of the smaller ideal is supplied. -/
theorem exists_curve_hilbert_degree_of_hilbert_comparison
    (I : Ideal (MvPolynomial σ K)) (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ K))
    (J : Ideal (MvPolynomial τ L)) {D : ℕ} (hD : HasCurveHilbertDegree J D)
    (hlower : ∀ n, n + 1 ≤ projectiveHilbertFunction I n)
    (hbound : ∀ n, projectiveHilbertFunction I n ≤ projectiveHilbertFunction J n) :
    ∃ D' : ℕ, D' ≤ D ∧ HasCurveHilbertDegree I D' := by
  obtain ⟨hDpos, b, M, hM⟩ := hD
  let p := projectiveHilbertPolynomial I hI
  obtain ⟨N, hN⟩ := projectiveHilbertPolynomial_spec I hI
  let c := D + b.natAbs + 1
  have hbabs : (b : ℚ) ≤ (b.natAbs : ℚ) := by
    simpa only [Int.cast_natCast] using (Int.cast_le (R := ℚ)).mpr (Int.le_natAbs (a := b))
  have hpbound (n : ℕ) (hn : max N M ≤ n) :
      0 ≤ p.eval (n : ℚ) ∧ p.eval (n : ℚ) ≤ (c : ℚ) * (n + 1) := by
    change 0 ≤ (projectiveHilbertPolynomial I hI).eval (n : ℚ) ∧ _
    rw [hN n (by omega)]
    have hle : (projectiveHilbertFunction I n : ℚ) ≤ projectiveHilbertFunction J n := by
      exact_mod_cast hbound n
    have he : (projectiveHilbertFunction J n : ℚ) = (D : ℚ) * n + b := by
      exact_mod_cast hM n (by omega)
    constructor
    · positivity
    · change (projectiveHilbertFunction I n : ℚ) ≤ ((D + b.natAbs + 1 : ℕ) : ℚ) * (n + 1)
      push_cast
      rw [he] at hle
      nlinarith [show (0 : ℚ) ≤ n by positivity, show (0 : ℚ) ≤ b.natAbs by positivity]
  have hp := polynomial_natDegree_le_one_of_nat_linear_bound p c (max N M) hpbound
  have hs := polynomial_slope_bounds p hp c (max N M) hpbound
  let q : Polynomial ℚ := p - (X + 1)
  have hq : q.natDegree ≤ 1 := by
    apply (natDegree_sub_le p (X + 1)).trans
    apply max_le hp
    simpa only [← C_1] using (natDegree_X_add_C (1 : ℚ)).le
  have hqbound (n : ℕ) (hn : max N M ≤ n) :
      0 ≤ q.eval (n : ℚ) ∧ q.eval (n : ℚ) ≤ (c : ℚ) * (n + 1) := by
    have hlo : (n : ℚ) + 1 ≤ p.eval (n : ℚ) := by
      change (n : ℚ) + 1 ≤ (projectiveHilbertPolynomial I hI).eval (n : ℚ)
      rw [hN n (by omega)]
      exact_mod_cast hlower n
    have hup := (hpbound n hn).2
    dsimp only [q]
    simp only [eval_sub, eval_add, eval_X, eval_one]
    constructor <;> nlinarith [show (0 : ℚ) ≤ n by positivity]
  have hspos : 1 ≤ p.coeff 1 := by
    have he := (polynomial_slope_bounds q hq c (max N M) hqbound).1
    dsimp only [q] at he
    norm_num [Polynomial.coeff_one] at he
    linarith
  obtain ⟨D', b', hD'coeff, _hb', hlin⟩ := polynomial_integer_linear_data
    (projectiveHilbertFunction I) p hp hs.1 N hN
  have hD'pos : 0 < D' := by
    have he : (1 : ℚ) ≤ D' := by rw [hD'coeff]; exact hspos
    have hn : 1 ≤ D' := by exact_mod_cast he
    omega
  have hD' : HasCurveHilbertDegree I D' := ⟨hD'pos, b', N, hlin⟩
  exact ⟨D', curveHilbertDegree_le_of_hilbertFunction_le _ _ hbound
    ⟨hDpos, b, M, hM⟩ hD', hD'⟩

end DimensionFourDependence
